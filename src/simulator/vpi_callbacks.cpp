#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/net.h"
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_internal.h"

namespace delta {

namespace {

// §36.10.2 / §37.43 / §38.36.1 / §38.36.1.1: the placement rules that do not
// depend on simulator timing state. Each returns the rejection message for the
// first rule the registration violates, or an empty string when none apply.
const char* VpiCheckCallbackPlacement(const VpiCbData& data,
                                      VpiToolPhase tool_phase) {
  // §36.10.2: while VPI functionality is restricted - the startup phase, and
  // the sizetf phase after it that permits no additional access - a callback
  // may be registered only for the six early-phase reasons. Reject any other
  // reason rather than register a callback the phase does not allow.
  if (VpiPhaseRestrictsFunctionality(tool_phase) &&
      !VpiStartupCallbackReasonAllowed(data.reason)) {
    return "vpi_register_cb() may register only an early-phase callback reason "
           "while VPI functionality is restricted";
  }

  // §37.43 detail 2: it is illegal to place a value change callback on an
  // automatic variable - automatic storage exists only while its frame is
  // active, so there is no persistent object to watch. Reject the registration.
  if (data.reason == cbValueChange && data.obj && data.obj->automatic) {
    return "vpi_register_cb(): a value change callback may not be placed on an "
           "automatic variable";
  }

  // §38.36.1: it is illegal to place a cbForce, cbRelease, or cbDisable
  // simulation-event callback on a variable bit-select. A single addressed bit
  // of a variable is not a legal target for a force/release/disable callback,
  // so reject the registration instead of handing back a callback that could
  // never fire correctly.
  if ((data.reason == cbForce || data.reason == cbRelease ||
       data.reason == cbDisable) &&
      data.obj && data.obj->type == vpiBitSelect) {
    return "vpi_register_cb(): a cbForce, cbRelease, or cbDisable callback may "
           "not "
           "be placed on a variable bit-select";
  }

  // §38.36.1.1: placing a cbStmt callback on a statement that resides in a
  // protected portion of the code is not allowed. Such a statement is sealed
  // behind encryption, so a per-statement callback cannot be placed on it;
  // reject the registration with a null handle and a recorded error message.
  if (data.reason == cbStmt && data.obj && data.obj->is_protected) {
    return "vpi_register_cb(): a cbStmt callback may not be placed on a "
           "statement "
           "in a protected portion of the code";
  }

  // §38.36.1.2: "Every possible object within the stmt class qualifies for
  // having a cbStmt callback placed on it. Each possible object is listed in
  // Table 38-6" - and the table is what §38.36.1.1 points the obj field at for
  // "the allowable objects". A handle to an object of any other kind names no
  // statement this callback could be called before, so the registration is
  // refused rather than answered with a callback nothing could ever fire. The
  // one handle in the field that is not a statement is a module instance, which
  // §38.36.1.3 defines as placing the callback on every statement the instance
  // holds rather than on the module itself.
  if (data.reason == cbStmt && data.obj && data.obj->type != kVpiModule &&
      !VpiIsScopeBodyStmtType(data.obj->type)) {
    return "vpi_register_cb(): a cbStmt callback may be placed only on one of "
           "the statement objects Table 38-6 lists, or on a module instance";
  }

  return nullptr;
}

// §38.36.2: a simulation-time callback carries its timing in the s_cb_data
// time structure, and the standard constrains how that structure - and a delay
// of zero - may be used. These checks apply only to the time-related reasons;
// every other reason ignores the time field. Returns the rejection message for
// the first rule violated, or an empty string when the timing is acceptable.
const char* VpiCheckCallbackTiming(const VpiCbData& data,
                                   bool sim_progressed_into_time_slice,
                                   int current_callback_reason,
                                   bool at_read_only_synch_time) {
  if (!VpiIsSimulationTimeCallbackReason(data.reason)) return nullptr;

  // §38.36.2: the time->type field shall be vpiSimTime or vpiScaledRealTime.
  // A vpiSuppressTime type, or a null time pointer, leaves no time for the
  // callback to fire at, so registration is an error and no callback is made.
  if (data.time == nullptr || data.time->type == vpiSuppressTime) {
    return "vpi_register_cb(): a simulation-time callback requires a time "
           "structure with type vpiSimTime or vpiScaledRealTime";
  }

  // §38.36.2: the requested time, or the delay before the callback, lives in
  // time->{low,high,real}; a delay of zero is all three being zero.
  bool delay_is_zero =
      data.time->low == 0 && data.time->high == 0 && data.time->real == 0.0;

  // §38.36.2: a zero-delay cbAtStartOfSimTime callback may not be placed once
  // simulation has progressed into a time slice - unless the application is
  // itself running inside a cbAtStartOfSimTime callback, where it is allowed
  // and produces another cbAtStartOfSimTime callback in the same time slice.
  if (data.reason == cbAtStartOfSimTime && delay_is_zero &&
      sim_progressed_into_time_slice &&
      current_callback_reason != cbAtStartOfSimTime) {
    return "vpi_register_cb(): a zero-delay cbAtStartOfSimTime callback may "
           "not "
           "be placed after simulation has entered a time slice, except from "
           "within a cbAtStartOfSimTime callback";
  }

  // §38.36.2: a zero-delay cbReadWriteSynch callback may not be placed at
  // read-only synch time, where scheduling an event for the current time is
  // not permitted.
  if (data.reason == cbReadWriteSynch && delay_is_zero &&
      at_read_only_synch_time) {
    return "vpi_register_cb(): a zero-delay cbReadWriteSynch callback may not "
           "be "
           "placed at read-only synch time";
  }

  return nullptr;
}

}  // namespace

bool VpiIsCallbackHostType(int type) {
  // §37.80 (figure): the objects the diagram draws a single arrow from to
  // `callback` - a prim term, an expr, a time queue and a stmt. Two of the four
  // are drawn in dotted enclosures, which §37.4.1 makes classes grouping other
  // objects and classes rather than kinds, so what they stand for is every kind
  // §37.59 draws in `expr` and every kind the `stmt` class groups.
  return type == vpiPrimTerm || type == kVpiTimeQueue || VpiIsExprType(type) ||
         VpiIsScopeBodyStmtType(type);
}

// §37.80 (figure) + detail 2: collect the callback objects an iteration
// reaches. With a reference object those are the callbacks registered on it -
// each registered callback whose s_cb_data obj field names it. With none they
// are the callbacks "not related to the above objects", which is what detail 2
// gives the NULL-reference form: every callback the diagram's single arrow
// leaves unreachable, because it was placed on no object at all or on one of a
// kind that arrow is not drawn from. That form handed back every callback the
// run held, the ones a prim term, an expr, a time queue or a stmt reaches
// included, so the iteration detail 2 defines for the rest was the whole
// registry.
//
// A callback object is not a child of the object it was placed on, so both
// forms are answered from the callback registry rather than by the generic
// child walk.
void VpiCollectCallbackObjects(VpiHandle ref,
                               const std::vector<VpiHandle>& cb_handles,
                               const std::vector<VpiCbData>& callbacks,
                               VpiHandle iter) {
  for (auto* cb_obj : cb_handles) {
    int idx = cb_obj->index;
    if (idx < 0 || idx >= static_cast<int>(callbacks.size())) continue;
    VpiHandle placed_on = callbacks[idx].obj;
    if (ref == nullptr) {
      if (placed_on == nullptr || !VpiIsCallbackHostType(placed_on->type)) {
        iter->children.push_back(cb_obj);
      }
      continue;
    }
    // §37.2.3: "Handle equivalence cannot be determined with a C '=='
    // comparison. The function vpi_compare_objects() compares the objects they
    // refer to." A callback is placed on an object, not on the handle the
    // application happened to register it through, so a second handle to that
    // object has to find it - and pointer equality found it only through the
    // one handle.
    if (GetGlobalVpiContext().CompareObjects(placed_on, ref) != 0) {
      iter->children.push_back(cb_obj);
    }
  }
}

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;

  const char* placement_error = VpiCheckCallbackPlacement(*data, tool_phase_);
  if (placement_error != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = placement_error;
    return nullptr;
  }

  const char* timing_error = VpiCheckCallbackTiming(
      *data, sim_progressed_into_time_slice_, current_callback_reason_,
      at_read_only_synch_time_);
  if (timing_error != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = timing_error;
    return nullptr;
  }

  callbacks_.push_back(*data);

  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->index = static_cast<int>(callbacks_.size() - 1);
  cb_handles_.push_back(cb_obj);

  // §37.80 (figure): a prim term, an expr, a time queue and a stmt each draw a
  // single arrow to `callback`, which §37.4.3 makes vpi_handle(vpiCallback,
  // obj) - the callback that object was given. It reached nothing: a callback
  // object lives in this registry rather than among the object's children, and
  // the walk that serves an untagged relation looks for a child whose own type
  // is the relation's. The object holds it from here, the arrow being
  // one-to-one and so reaching the first callback the object was given.
  if (data->obj != nullptr && VpiIsCallbackHostType(data->obj->type) &&
      data->obj->callback == nullptr) {
    data->obj->callback = cb_obj;
  }
  return cb_obj;
}

int VpiContext::RemoveCb(VpiHandle cb_handle) {
  // §38.39: the argument shall be a handle to the callback object. A null or
  // wrong-typed handle is not a callback object, so removal fails.
  if (!cb_handle) return 0;
  if (cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx >= 0 && idx < static_cast<int>(callbacks_.size())) {
    // §38.39: once vpi_remove_cb() has been called with a handle to the
    // callback, that handle is no longer valid. A cleared reason marks an
    // already-removed slot, so a repeat removal on the stale handle fails
    // rather than reporting success a second time.
    if (callbacks_[idx].reason < 0) return 0;
    callbacks_[idx].reason = -1;
    // §37.2.2: "Handles may also be released as part of the action of other VPI
    // function calls, in particular: a) vpi_remove_callback() releases the
    // associated callback handle." Clearing the registration is what stops the
    // callback from being delivered; releasing the handle is what stops it
    // being a live handle to the callback object, which the clause has this
    // routine do and which nothing did - so a removed callback's handle went on
    // naming a live object and every routine went on accepting it.
    ReleaseHandle(cb_handle);
    // §37.80: with the handle released, the object that reached this callback
    // through the diagram's single arrow reaches it no longer.
    VpiHandle placed_on = callbacks_[idx].obj;
    if (placed_on != nullptr && placed_on->callback == cb_handle) {
      placed_on->callback = nullptr;
    }
    return 1;
  }
  return 0;
}

int VpiContext::ExecuteCallback(VpiHandle cb_handle) {
  if (!cb_handle || cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx < 0 || idx >= static_cast<int>(callbacks_.size())) return 0;
  VpiCbData& cb = callbacks_[idx];
  // §38.36: the simulator executes the callback by invoking the cb_rtn the
  // application supplied, passing it a pointer to the s_cb_data structure
  // (which belongs to the simulator). With no cb_rtn there is nothing to
  // invoke.
  if (!cb.cb_rtn) return 0;
  return cb.cb_rtn(&cb);
}

void VpiContext::RegisterCbValueChange(const VpiCbData& data) {
  if (!data.obj || !data.obj->var) return;
  void* user_data = data.user_data;
  data.obj->var->AddWatcher([user_data]() {
    if (user_data) *static_cast<bool*>(user_data) = true;
    return true;
  });
}

// §38.36.1.3: collect every statement within a module instance that can have a
// cbStmt callback placed on it. The statement-class objects reached through the
// module's children qualify - the same kinds a scope body groups (§37.12) - and
// the recursion descends through them so a statement nested inside a block is
// found as well. Two kinds of child are left out. A nested module instance owns
// its own statements, so the walk does not cross into one. And a statement that
// resides in a protected portion of the code shall not have a callback placed
// on it, so a protected child - which seals everything it contains - is skipped
// in whole.
static void VpiCollectModuleWideStmtTargets(VpiObject* scope,
                                            std::vector<VpiObject*>& out) {
  for (VpiObject* child : scope->children) {
    if (child == nullptr) continue;
    if (child->is_protected) continue;
    if (child->type == kVpiModule) continue;
    if (VpiIsScopeBodyStmtType(child->type)) out.push_back(child);
    VpiCollectModuleWideStmtTargets(child, out);
  }
}

namespace {

// §38.36.1.1: the s_cb_data delivered for a cbStmt callback has fixed contents
// regardless of what was supplied at registration - the value field is always
// NULL and the index field is always 0. In addition, when the callback was
// registered with a vpiSuppressTime time type, no time is passed to the routine
// and the time pointer is set to NULL. A non-cbStmt callback is left untouched.
//
// Otherwise the routine is passed a time structure "which will contain the
// current simulation time, of the type ... indicated in the call to
// vpi_register_cb()". At registration "only the type is used", so the structure
// the application supplied there says which form to deliver and nothing about
// when: the time itself is read here, as the statement is about to execute. It
// goes into storage the dispatch owns, because the structure the routine sees
// is not the registration's and writing through that pointer would overwrite
// the request. vpiScaledRealTime is scaled to the timescale of the statement in
// the obj field, the object this delivery is about.
void VpiNormalizeCbStmtData(VpiCbData& data, VpiTime& delivered,
                            VpiContext& ctx) {
  if (data.reason != cbStmt) return;
  data.value = nullptr;
  data.index = 0;
  if (data.time == nullptr) return;
  if (data.time->type == vpiSuppressTime) {
    data.time = nullptr;
    return;
  }
  delivered.type = data.time->type;
  ctx.GetTime(delivered.type == kVpiScaledRealTime ? data.obj : nullptr,
              &delivered);
  data.time = &delivered;
}

// §38.36.1: shape the s_cb_data fields that a simulation-event callback
// delivers with a fixed value regardless of what was requested at registration.
void VpiNormalizeSimEventCbData(VpiCbData& data) {
  // Two reasons carry no simulation time to the routine. A cbReclaimObj
  // callback has no relationship to simulation time, so its time field is
  // delivered as NULL; and for both cbReclaimObj and cbEndOfObject the
  // time->type supplied at registration is ignored because no time is passed.
  // Drop the time pointer so the routine observes the absence of time rather
  // than a stale request. Any other reason keeps whatever time was requested.
  if (data.reason == cbReclaimObj || data.reason == cbEndOfObject) {
    data.time = nullptr;
  }

  // A cbValueChange callback delivers a NULL value field when the watched
  // object has no value that can be read through that field. An event
  // statement has no value at all, and a class variable holds an opaque handle
  // to a dynamic object whose value cannot be obtained this way (the object it
  // refers to is identified through vpiObjId instead). In either case the
  // routine sees value = NULL rather than the format requested at registration.
  // A cbValueChange on an ordinary object keeps its value field.
  if (data.reason == cbValueChange && data.obj != nullptr &&
      (data.obj->type == vpiEventStmt || data.obj->type == vpiNamedEvent ||
       data.obj->type == vpiClassVar)) {
    data.value = nullptr;
  }
}

// §38.36.2: shape the s_cb_data a simulation-time callback delivers. "When a
// simulation time callback occurs, the application callback routine shall be
// passed a single argument, which is a pointer to an s_cb_data structure [this
// is not a pointer to the same structure that was passed to
// vpi_register_cb()]. The time structure shall contain the current simulation
// time", and "the value fields are ignored for all reasons with simulation
// time callbacks".
//
// The routine was passed the time the registration asked the callback to fire
// at, which is the delay or the requested moment rather than the time the
// simulation is at when it fires, and it was passed whatever value the
// registration carried. The current time goes into storage the dispatch owns:
// the structure the routine sees is not the registration's, so writing through
// the pointer the registration supplied would overwrite the request. The
// requested form is kept, vpiSimTime delivering the raw count and
// vpiScaledRealTime a real scaled to the timescale of the obj field, which
// §38.36.2 names as "the object for determining the time scaling".
void VpiNormalizeSimTimeCbData(VpiCbData& data, VpiTime& delivered,
                               VpiContext& ctx) {
  if (!VpiIsSimulationTimeCallbackReason(data.reason)) return;
  delivered.type = data.time != nullptr ? data.time->type : kVpiSimTime;
  ctx.GetTime(delivered.type == kVpiScaledRealTime ? data.obj : nullptr,
              &delivered);
  data.time = &delivered;
  data.value = nullptr;
}

// §38.36.1.3: report whether this delivery targets a module instance through a
// cbStmt callback, which must fan out to every statement in the module rather
// than fire once for the module as a whole.
bool VpiIsModuleWideCbStmt(const VpiCbData& data) {
  return data.reason == cbStmt && data.obj != nullptr &&
         data.obj->type == kVpiModule;
}

}  // namespace

int VpiContext::DispatchCallbacks(int reason, VpiHandle obj, void* user_data) {
  int fired = 0;
  // §38.36.3: only callbacks still registered for this reason are delivered.
  // RemoveCb marks a removed callback by clearing its reason, so a removed slot
  // never matches a real reason here. Snapshot the count so callbacks
  // registered from within a routine are not delivered during this same pass.
  size_t count = callbacks_.size();

  // Deliver one invocation of a callback routine. `data` already carries the
  // obj the routine should see. This applies the cbStmt field guarantees
  // (§38.36.1.1) and the current-reason bookkeeping (§38.9), then counts the
  // firing.
  auto deliver = [&](VpiCbData data) {
    // §38.36.1.1: apply the fixed s_cb_data field contents a cbStmt callback
    // requires before the routine sees them, and the current simulation time it
    // is passed in the form the registration asked for.
    VpiTime delivered_stmt_time;
    VpiNormalizeCbStmtData(data, delivered_stmt_time, *this);
    // §38.36.1: a cbReclaimObj or cbEndOfObject callback is passed no time, so
    // clear the time pointer before the routine runs.
    VpiNormalizeSimEventCbData(data);
    // §38.36.2: a simulation-time callback is passed the current simulation
    // time and no value.
    VpiTime delivered_time;
    VpiNormalizeSimTimeCbData(data, delivered_time, *this);
    // §38.9: record the reason of the routine about to run so that a routine
    // gated on its callback reason (e.g. vpi_get_data, legal only under
    // cbStartOfRestart/cbEndOfRestart) can observe it. Restore the prior value
    // afterward to keep nested dispatches honest.
    int saved_reason = current_callback_reason_;
    current_callback_reason_ = data.reason;
    data.cb_rtn(&data);
    current_callback_reason_ = saved_reason;
    ++fired;
  };

  for (size_t i = 0; i < count; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    // §38.36.3: the routine is passed a pointer to an s_cb_data structure that
    // is not the one supplied at registration. Work from a copy and let the
    // simulator fill obj/user_data when it has them for this reason.
    VpiCbData data = callbacks_[i];
    if (obj != nullptr) {
      data.obj = obj;
    }
    if (user_data != nullptr) {
      data.user_data = user_data;
    }
    // §38.36.1.3: a handle to a module instance in the obj field places a
    // cbStmt callback on every statement in the module that can have one. The
    // single registration stands in for all of them, so deliver the routine
    // once per such statement - each with obj set to that statement - rather
    // than once for the module as a whole. Statements in protected portions are
    // skipped by the collector and never receive a callback.
    if (VpiIsModuleWideCbStmt(data)) {
      std::vector<VpiObject*> stmts;
      VpiCollectModuleWideStmtTargets(data.obj, stmts);
      for (VpiObject* stmt : stmts) {
        VpiCbData per = data;
        per.obj = stmt;
        deliver(per);
      }
      continue;
    }
    deliver(data);
  }
  return fired;
}

void VpiContext::NoteErrorRecorded() {
  // §36.10.1: an error is what the callbacks are set up for, so a routine that
  // recorded none has nothing to deliver.
  if (last_error_.level == 0) return;
  // An error callback is an application, so the VPI routines it calls record
  // errors of their own on the way out. A pass already running is what those
  // land in the middle of, and delivering a second pass from inside the first
  // would have the same application called again for the error its own call
  // raised, without end.
  if (dispatching_error_callbacks_) return;

  dispatching_error_callbacks_ = true;
  // §38.36.3: "cbPLIError -- simulation run-time error occurred in a PLI
  // function call", against cbError's "simulation run-time error occurred". The
  // state §38.2 gives the error is what separates them.
  DispatchCallbacks(last_error_.state == kVpiPLI ? kCbPLIError : kCbError);
  dispatching_error_callbacks_ = false;
}

int VpiContext::DispatchReset() {
  // §38.33: a reset drops the user-data stored on every call instance before
  // the reset callbacks run, so a vpi_get_userdata() during cbEndOfReset starts
  // from null until the application sets the field again.
  ClearUserDataForRestartOrReset();
  int fired = DispatchCallbacks(kCbStartOfReset);
  fired += DispatchCallbacks(kCbEndOfReset);
  return fired;
}

int VpiContext::DispatchRestart() {
  // §37.2.2 (restart): a simulation restart releases all handles except the
  // handles to the cbStartOfRestart and cbEndOfRestart callbacks. Apply this
  // before the callback reasons are cleared below, so the surviving restart
  // callbacks are still identifiable by their reason.
  ReleaseHandlesForRestart();

  // §38.33: a restart drops the user-data stored on every call instance, so a
  // vpi_get_userdata() after the restart returns null until the application
  // re-establishes the field (e.g. from a cbEndOfRestart routine).
  ClearUserDataForRestartOrReset();

  // §38.36.3: with the exception of the restart callbacks, every registered
  // callback is removed when a restart occurs. Clearing the reason marks a slot
  // removed, matching RemoveCb.
  for (VpiCbData& slot : callbacks_) {
    if (slot.reason != kCbStartOfRestart && slot.reason != kCbEndOfRestart) {
      slot.reason = -1;
    }
  }
  int fired = DispatchCallbacks(kCbStartOfRestart);
  fired += DispatchCallbacks(kCbEndOfRestart);
  return fired;
}

int VpiContext::SmallestModuleTimePrecision() const {
  // §37.10 detail 7: gather the precision of every module in the design and
  // return the smallest one.
  std::vector<int> precisions;
  for (const VpiObject* candidate : all_objects_) {
    if (candidate->type == kVpiModule) {
      precisions.push_back(candidate->time_precision);
    }
  }
  return VpiSmallestTimePrecision(precisions);
}

}  // namespace delta
