#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §36.10.2 / §37.43 / §38.36.1 / §38.36.1.1: the placement rules that do not
// depend on simulator timing state. Each returns the rejection message for the
// first rule the registration violates, or an empty string when none apply.
// §38.36.1 with §37.17 detail 13: whether `obj` is a bit-select of a
// variable, a var bit among them; a net's bits are net bits.
bool IsVariableBitSelect(const VpiObject& obj) {
  return obj.type == vpiBitSelect || obj.type == vpiVarBit;
}

const char* VpiCheckCallbackPlacement(const s_cb_data& data,
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
  if (data.reason == cbValueChange && data.obj &&
      VpiObjectOf(data.obj)->automatic) {
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
      data.obj && IsVariableBitSelect(*VpiObjectOf(data.obj))) {
    return "vpi_register_cb(): a cbForce, cbRelease, or cbDisable callback may "
           "not "
           "be placed on a variable bit-select";
  }

  // §38.36.1.1: placing a cbStmt callback on a statement that resides in a
  // protected portion of the code is not allowed. Such a statement is sealed
  // behind encryption, so a per-statement callback cannot be placed on it;
  // reject the registration with a null handle and a recorded error message.
  if (data.reason == cbStmt && data.obj &&
      VpiObjectOf(data.obj)->is_protected) {
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
  if (data.reason == cbStmt && data.obj &&
      VpiObjectOf(data.obj)->type != kVpiModule &&
      !VpiIsScopeBodyStmtType(VpiObjectOf(data.obj)->type)) {
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
const char* VpiCheckCallbackTiming(const s_cb_data& data,
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
                               const std::vector<s_cb_data>& callbacks,
                               VpiHandle iter) {
  for (auto* cb_obj : cb_handles) {
    int idx = cb_obj->index;
    if (idx < 0 || idx >= static_cast<int>(callbacks.size())) continue;
    VpiHandle placed_on = VpiObjectOf(callbacks[idx].obj);
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

namespace {

// §38.36.1: whether a `reason` registration placed on `obj` is still live
// among `callbacks`.
bool IsPlacedOn(const std::vector<s_cb_data>& callbacks, int reason,
                const VpiObject* obj) {
  return std::ranges::any_of(callbacks, [reason, obj](const s_cb_data& cb) {
    return cb.reason == reason && cb.obj != nullptr &&
           VpiObjectOf(cb.obj) == obj;
  });
}

// Whether any `reason` registration is still live among `callbacks`.
bool HasCallbackFor(const std::vector<s_cb_data>& callbacks, int reason) {
  return std::ranges::any_of(
      callbacks, [reason](const s_cb_data& cb) { return cb.reason == reason; });
}

// The aval and bval words of the bits `obj` stands for: its variable's, or,
// for a bit or a select of one, those of its parent's it spans.
std::vector<uint64_t> ObjectBits(const VpiObject& obj) {
  const Logic4Vec& whole = obj.var->value;
  std::vector<uint64_t> bits;
  if (obj.bit_offset < 0) {
    for (uint32_t i = 0; i < whole.nwords; ++i) {
      bits.push_back(whole.words[i].aval);
      bits.push_back(whole.words[i].bval);
    }
    return bits;
  }
  for (int k = 0; k < std::max(obj.size, 1); ++k) {
    const auto kBit = static_cast<uint32_t>(obj.bit_offset + k);
    if (kBit / 64 >= whole.nwords) break;
    bits.push_back((whole.words[kBit / 64].aval >> (kBit % 64)) & 1);
    bits.push_back((whole.words[kBit / 64].bval >> (kBit % 64)) & 1);
  }
  return bits;
}

// §38.36.1 with §37.17 detail 14: watch the storage of `obj` and, as it is
// written, call back the cbSizeChange registrations placed on it where its
// size changed, then the cbValueChange ones where its value did, a write of
// what it holds being no change, until none of either is left.
void WatchObjectChanges(VpiContext& vpi, VpiObject* obj) {
  if (obj == nullptr || obj->var == nullptr || obj->value_change_watched) {
    return;
  }
  obj->value_change_watched = true;
  obj->var->AddWatcher([&vpi, obj, held = ObjectBits(*obj),
                        size = vpi.Get(vpiSize, obj)]() mutable {
    const auto& callbacks = vpi.RegisteredCallbacks();
    const bool kSizes = IsPlacedOn(callbacks, cbSizeChange, obj);
    const bool kValues = IsPlacedOn(callbacks, cbValueChange, obj);
    if (!kSizes && !kValues) {
      obj->value_change_watched = false;
      return true;
    }
    const int kSize = vpi.Get(vpiSize, obj);
    if (kSize != size) {
      size = kSize;
      if (kSizes) vpi.DispatchCallbacks(cbSizeChange, obj);
    }
    std::vector<uint64_t> now = ObjectBits(*obj);
    if (now == held) return false;
    held = std::move(now);
    if (kValues) vpi.DispatchCallbacks(cbValueChange, obj);
    return false;
  });
}

// The model's object for the statement `stmt` run in the instance `prefix`
// names, among `stmts`: one a run names with a dot after it and the model
// without, and found under any instance writing it where the model keyed it
// under another name; null where the model holds none.
VpiObject* StmtObjectFor(const VpiStmtObjects& stmts, const Stmt* stmt,
                         std::string prefix) {
  if (stmt == nullptr) return nullptr;
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  auto found = stmts.find({stmt, prefix});
  if (found == stmts.end()) found = stmts.lower_bound({stmt, std::string()});
  if (found == stmts.end() || found->first.first != stmt) return nullptr;
  return found->second;
}

// §38.36.2: the delay a simulation-time callback's time gives, in ticks of
// the simulation time unit `sim_unit`: a vpiScaledRealTime one in the time
// unit of the callback's object, or the simulation time unit without one.
uint64_t CallbackDelayTicks(const s_cb_data& data, int sim_unit) {
  if (data.time == nullptr) return 0;
  if (data.time->type == kVpiScaledRealTime && data.obj == nullptr) {
    return static_cast<uint64_t>(std::llround(data.time->real));
  }
  if (data.time->type == kVpiScaledRealTime) {
    return VpiPutDelayTicks(*VpiObjectOf(data.obj), *data.time, sim_unit);
  }
  return (uint64_t{data.time->high} << 32) | data.time->low;
}

// §38.36.2 with §4.4.3: schedule the simulation-time callback `cb`, of the
// registration `data`, in the run `scheduler` holds: an event at its time, in
// the PLI region its reason runs in, that calls it once. A cbNextSimTime is
// called from the run loop instead, before the first slot after this one.
void ScheduleTimeCallback(VpiContext& vpi, Scheduler& scheduler, VpiObject* cb,
                          const s_cb_data& data) {
  cb->event_time = scheduler.CurrentTime().ticks;
  if (data.reason == cbNextSimTime) return;
  Event* queued = scheduler.GetEventPool().Acquire();
  queued->callback = [&vpi, cb]() { vpi.DeliverCallback(cb); };
  scheduler.ScheduleEvent(
      SimTime{cb->event_time + CallbackDelayTicks(data, vpi.SimTimeUnit())},
      RegionForPliCallback(data.reason), queued);
}

}  // namespace

VpiHandle VpiContext::RegisterCb(s_cb_data* data) {
  if (!data) return nullptr;

  const char* placement_error = VpiCheckCallbackPlacement(*data, tool_phase_);
  if (placement_error != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(placement_error);
    return nullptr;
  }

  const char* timing_error = VpiCheckCallbackTiming(
      *data, sim_progressed_into_time_slice_, current_callback_reason_,
      at_read_only_synch_time_);
  if (timing_error != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(timing_error);
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
  if (data->obj != nullptr &&
      VpiIsCallbackHostType(VpiObjectOf(data->obj)->type) &&
      VpiObjectOf(data->obj)->callback == nullptr) {
    VpiObjectOf(data->obj)->callback = cb_obj;
  }
  if ((data->reason == cbValueChange || data->reason == cbSizeChange) &&
      data->obj != nullptr) {
    WatchObjectChanges(*this, VpiObjectOf(data->obj));
  }
  if (data->reason == cbStmt) stmt_callbacks_registered_ = true;
  if (scheduler_ != nullptr &&
      VpiIsSimulationTimeCallbackReason(data->reason)) {
    ScheduleTimeCallback(*this, *scheduler_, cb_obj, *data);
  }
  return cb_obj;
}

// The three accessors below are defined here rather than in the class because
// src/simulator/vpi_context.h is one class declaration standing at the line
// count assert-no-oversized-source-files leaves a file, so what is added to it
// has to be paid for out of it. Their comments stay with the declarations,
// where a reader looks for them; this file is where callbacks_ and the time
// slice flags are read and written anyway.
const std::vector<s_cb_data>& VpiContext::RegisteredCallbacks() const {
  return callbacks_;
}

void VpiContext::SetSimulationProgressedIntoTimeSlice(bool progressed) {
  sim_progressed_into_time_slice_ = progressed;
}

bool VpiContext::SimulationProgressedIntoTimeSlice() const {
  return sim_progressed_into_time_slice_;
}

VpiHandle VpiContext::CreateAssertionCallbackObject(
    std::uint64_t placed_handle) {
  // §39.4.2: a placed assertion callback answers with a handle to the callback,
  // which is a callback object like the one vpi_register_cb() answers with. It
  // carries no index into the simulation-callback table: what it stands for is
  // the placement in the assertion model, which is what `assertion_cb_handle`
  // names and what vpi_remove_cb() removes.
  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->is_assertion_cb = true;
  cb_obj->assertion_cb_handle = placed_handle;
  // §38.39 reads `index` as the row of the simulation callback table a handle
  // stands for, and this handle stands for no row of it. -1 is the value that
  // names none, so a removal that reaches §38.39 with this handle removes
  // nothing rather than whatever registration happens to sit in row zero.
  cb_obj->index = -1;
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
    VpiHandle placed_on = VpiObjectOf(callbacks_[idx].obj);
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
  s_cb_data& cb = callbacks_[idx];
  // §38.36: the simulator executes the callback by invoking the cb_rtn the
  // application supplied, passing it a pointer to the s_cb_data structure
  // (which belongs to the simulator). With no cb_rtn there is nothing to
  // invoke.
  if (!cb.cb_rtn) return 0;
  return cb.cb_rtn(&cb);
}

void VpiContext::RegisterCbValueChange(const s_cb_data& data) {
  if (!data.obj || !VpiObjectOf(data.obj)->var) return;
  void* user_data = data.user_data;
  VpiObjectOf(data.obj)->var->AddWatcher([user_data]() {
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
void VpiNormalizeCbStmtData(s_cb_data& data, s_vpi_time& delivered,
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
  ctx.GetTime(
      delivered.type == kVpiScaledRealTime ? VpiObjectOf(data.obj) : nullptr,
      &delivered);
  data.time = &delivered;
}

// §38.36.1: shape the s_cb_data fields that a simulation-event callback
// delivers with a fixed value regardless of what was requested at registration.
void VpiNormalizeSimEventCbData(s_cb_data& data) {
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
      (VpiObjectOf(data.obj)->type == vpiEventStmt ||
       VpiObjectOf(data.obj)->type == vpiNamedEvent ||
       VpiObjectOf(data.obj)->type == vpiClassVar)) {
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
void VpiNormalizeSimTimeCbData(s_cb_data& data, s_vpi_time& delivered,
                               VpiContext& ctx) {
  if (!VpiIsSimulationTimeCallbackReason(data.reason)) return;
  delivered.type = data.time != nullptr ? data.time->type : kVpiSimTime;
  ctx.GetTime(
      delivered.type == kVpiScaledRealTime ? VpiObjectOf(data.obj) : nullptr,
      &delivered);
  data.time = &delivered;
  data.value = nullptr;
}

// §38.36.1.3: report whether this delivery targets a module instance through a
// cbStmt callback, which must fan out to every statement in the module rather
// than fire once for the module as a whole.
bool VpiIsModuleWideCbStmt(const s_cb_data& data) {
  return data.reason == cbStmt && data.obj != nullptr &&
         VpiObjectOf(data.obj)->type == kVpiModule;
}

// §38.36.1.3: report whether a cbStmt registration placed a callback on the
// statement the dispatch names. The obj field of the registration is what says
// where the callback was placed: on the statement that field names, or, where
// it names a module instance, on every statement in that instance which can
// have one. So a registration against another statement, or against a module
// instance this statement does not belong to, placed no callback where this
// statement is executing. A registration whose obj field named no object at
// all placed the callback on no statement in particular, and stands for
// whichever one the dispatch names.
bool VpiCbStmtIsPlacedOn(const s_cb_data& reg, VpiHandle stmt) {
  if (reg.obj == nullptr || VpiObjectOf(reg.obj) == stmt) return true;
  if (VpiObjectOf(reg.obj)->type != kVpiModule) return false;
  std::vector<VpiObject*> placed;
  VpiCollectModuleWideStmtTargets(VpiObjectOf(reg.obj), placed);
  for (VpiObject* target : placed) {
    if (target == stmt) return true;
  }
  return false;
}

// The name of the class whose typespec the class obj `obj` reaches; empty
// where it reaches none.
std::string_view ClassNameOf(const VpiObject& obj) {
  for (const VpiObject* child : obj.children) {
    if (child != nullptr && child->type == vpiClassTypespec) return child->name;
  }
  return {};
}

// §38.36.1: whether the registration `reg` placed no callback on `obj`, the
// object a delivery for `reason` is about: a cbStmt placed on another
// statement or another module's, or a cbValueChange placed on another object.
bool PlacedElsewhere(const s_cb_data& reg, int reason, VpiHandle obj) {
  if (obj == nullptr) return false;
  if (reason == cbStmt) return !VpiCbStmtIsPlacedOn(reg, obj);
  if (reg.obj == nullptr) return false;
  if (reason == cbValueChange || reason == cbSizeChange ||
      reason == cbDisable) {
    return VpiObjectOf(reg.obj) != obj;
  }
  if (reason == cbCreateObj) {
    return VpiObjectOf(reg.obj)->name != ClassNameOf(*obj);
  }
  return false;
}

// §38.36.1: the simulation-event reasons whose routine is given the time
// they occurred at.
bool IsTimedEventReason(int reason) {
  switch (reason) {
    case cbValueChange:
    case cbForce:
    case cbRelease:
    case cbSizeChange:
    case cbDisable:
    case cbCreateObj:
    case cbStartOfThread:
      return true;
    default:
      return false;
  }
}

// §38.36.1: the value a simulation-event callback's routine is given, in
// storage the dispatch owns: an object's new value for cbValueChange and its
// new size for cbSizeChange, in the format the registration asked for unless
// it asked for none; the forced object's value, which their dispatch reads,
// for cbForce and cbRelease; and none for a reason that carries no value.
void FillEventValue(s_cb_data& data, s_vpi_value& value, VpiContext& ctx,
                    VpiObject* obj) {
  if (data.reason == cbForce || data.reason == cbRelease) return;
  if (data.reason != cbValueChange && data.reason != cbSizeChange) {
    data.value = nullptr;
    return;
  }
  if (data.value == nullptr || data.value->format == vpiSuppressVal ||
      obj == nullptr) {
    return;
  }
  value.format = data.value->format;
  if (data.reason == cbSizeChange) {
    value.format = vpiIntVal;
    value.value.integer = ctx.Get(vpiSize, obj);
  } else {
    ctx.GetValue(obj, &value);
  }
  data.value = &value;
}

// §38.36.1: the routine of a simulation-event callback is given the current
// time in the type the registration asked for, unless it asked for none, the
// value FillEventValue gives, and, for a change of an array member, the
// member's index. Each goes into storage the dispatch owns.
void VpiFillSimEventCbData(s_cb_data& data, s_vpi_time& time,
                           s_vpi_value& value, VpiContext& ctx) {
  if (!IsTimedEventReason(data.reason)) return;
  VpiObject* obj = VpiObjectOf(data.obj);
  if (data.time != nullptr && data.time->type != vpiSuppressTime) {
    time.type = data.time->type;
    ctx.GetTime(time.type == kVpiScaledRealTime ? obj : nullptr, &time);
    data.time = &time;
  }
  FillEventValue(data, value, ctx, obj);
  if (data.reason == cbValueChange && obj != nullptr) {
    data.index = VpiVariableIsArrayMember(obj) ? obj->index : 0;
  }
}

// §38.36.2: whether the registration `i` among `callbacks` is a
// cbNextSimTime a run's `scheduler` holds that is not yet due: such a
// callback is called before the first time slot after the one it was
// registered in, and once, so a due one is taken off here.
bool NextSimTimeNotDue(std::vector<s_cb_data>& callbacks,
                       const std::vector<VpiObject*>& handles, size_t i,
                       const Scheduler* scheduler) {
  if (callbacks[i].reason != cbNextSimTime || scheduler == nullptr) {
    return false;
  }
  if (i >= handles.size() ||
      handles[i]->event_time >= scheduler->CurrentTime().ticks) {
    return true;
  }
  callbacks[i].reason = -1;
  return false;
}

// §38.36.3: the routine is passed a pointer to an s_cb_data structure that is
// not the one supplied at registration. The simulator fills in the obj and
// user_data fields where the dispatch has them for this reason, and leaves
// what the registration supplied in place where it does not.
void VpiApplyDispatchOverrides(s_cb_data& data, VpiHandle obj,
                               void* user_data) {
  if (obj != nullptr) data.obj = VpiHandleOf(obj);
  if (user_data != nullptr) data.user_data = static_cast<PLI_BYTE8*>(user_data);
}

}  // namespace

// Deliver one invocation of a callback routine. `data` already carries the obj
// the routine should see. This applies the cbStmt field guarantees
// (§38.36.1.1) and the current-reason bookkeeping (§38.9).
void VpiContext::Deliver(s_cb_data data) {
  // §38.36.1.1: apply the fixed s_cb_data field contents a cbStmt callback
  // requires before the routine sees them, and the current simulation time it
  // is passed in the form the registration asked for.
  s_vpi_time delivered_stmt_time{};
  VpiNormalizeCbStmtData(data, delivered_stmt_time, *this);
  // §38.36.1: a callback about an object's value is passed the time, the new
  // value and an array member's index.
  s_vpi_time delivered_event_time{};
  s_vpi_value delivered_value{};
  VpiFillSimEventCbData(data, delivered_event_time, delivered_value, *this);
  // §38.36.1: a cbReclaimObj or cbEndOfObject callback is passed no time, so
  // clear the time pointer before the routine runs.
  VpiNormalizeSimEventCbData(data);
  // §38.36.2: a simulation-time callback is passed the current simulation
  // time and no value.
  s_vpi_time delivered_time{};
  VpiNormalizeSimTimeCbData(data, delivered_time, *this);
  // §38.9: record the reason of the routine about to run so that a routine
  // gated on its callback reason (e.g. vpi_get_data, legal only under
  // cbStartOfRestart/cbEndOfRestart) can observe it. Restore the prior value
  // afterward to keep nested dispatches honest.
  int saved_reason = current_callback_reason_;
  current_callback_reason_ = data.reason;
  data.cb_rtn(&data);
  current_callback_reason_ = saved_reason;
}

void VpiContext::DispatchStmtCallbacks(const Stmt* stmt, std::string prefix) {
  if (!stmt_callbacks_registered_) return;
  VpiObject* obj = StmtObjectFor(stmt_objects_, stmt, std::move(prefix));
  if (obj != nullptr) DispatchCallbacks(cbStmt, obj);
}

void VpiContext::NoteThreadCreated(Process* proc) {
  // §38.36.1: a thread's object is made, and cbStartOfThread called for it
  // (ThreadObjectFor), as the run creates it.
  if (sim_ctx_ != nullptr && HasCallbackFor(callbacks_, cbStartOfThread)) {
    ThreadObjectFor(proc);
  }
}

void VpiContext::NoteObjectCreated(ClassObject& obj) {
  if (sim_ctx_ == nullptr || !HasCallbackFor(callbacks_, cbCreateObj)) return;
  DispatchCallbacks(cbCreateObj, MadeClassObject(obj));
}

void VpiContext::NoteForce(int reason, const Variable* var, const Stmt* stmt,
                           std::string prefix) {
  if (!HasCallbackFor(callbacks_, reason)) return;
  VpiObject* stmt_obj = StmtObjectFor(stmt_objects_, stmt, std::move(prefix));
  const size_t kCount = callbacks_.size();
  for (size_t i = 0; i < kCount; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    // §38.36.1: a callback placed on an object is called for a force or
    // release of that object, one placed on none for every one, its obj the
    // statement and its value the forced object's after the statement.
    VpiObject* placed = VpiObjectOf(callbacks_[i].obj);
    if (placed != nullptr && placed->var != var) continue;
    s_cb_data data = callbacks_[i];
    s_vpi_value value{};
    if (placed != nullptr && data.value != nullptr &&
        data.value->format != vpiSuppressVal) {
      value.format = data.value->format;
      GetValue(placed, &value);
      data.value = &value;
    }
    data.obj = VpiHandleOf(stmt_obj);
    Deliver(data);
  }
}

void VpiContext::NoteDisabled(std::string_view label, std::string prefix) {
  if (!HasCallbackFor(callbacks_, cbDisable)) return;
  // §38.36.1: the named begin or fork the disable names, among the blocks of
  // the instance it ran in.
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  const std::string_view kLeaf = label.substr(label.rfind('.') + 1);
  for (const auto& [key, obj] : stmt_objects_) {
    if (key.second == prefix && obj->name == kLeaf &&
        (obj->type == vpiNamedBegin || obj->type == vpiNamedFork)) {
      DispatchCallbacks(cbDisable, obj);
      return;
    }
  }
}

int VpiContext::DeliverCallback(VpiHandle cb_handle) {
  if (cb_handle == nullptr || cb_handle->type != kVpiCallback) return 0;
  const int kIndex = cb_handle->index;
  if (kIndex < 0 || kIndex >= static_cast<int>(callbacks_.size())) return 0;
  const s_cb_data kData = callbacks_[kIndex];
  if (kData.reason < 0 || kData.cb_rtn == nullptr) return 0;
  // §38.36.2: a simulation-time callback is called once, and a value may not
  // be written while a cbReadOnlySynch routine runs.
  if (IsOneShotPliCallback(kData.reason)) callbacks_[kIndex].reason = -1;
  const bool kSavedReadOnly = at_read_only_synch_time_;
  if (kData.reason == cbReadOnlySynch) at_read_only_synch_time_ = true;
  Deliver(kData);
  at_read_only_synch_time_ = kSavedReadOnly;
  return 1;
}

int VpiContext::DispatchCallbacks(int reason, VpiHandle obj, void* user_data) {
  int fired = 0;
  // §38.36.3: only callbacks still registered for this reason are delivered.
  // RemoveCb marks a removed callback by clearing its reason, so a removed slot
  // never matches a real reason here. Snapshot the count so callbacks
  // registered from within a routine are not delivered during this same pass.
  size_t count = callbacks_.size();

  for (size_t i = 0; i < count; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    // §38.36.1.3: a cbStmt callback is placed on particular statements, so
    // where the dispatch names the statement that is about to execute, only
    // the registrations that placed a callback on that statement are delivered
    // for it.
    if (PlacedElsewhere(callbacks_[i], reason, obj)) continue;
    if (NextSimTimeNotDue(callbacks_, cb_handles_, i, scheduler_)) continue;
    // §38.36.3: the routine is passed a pointer to an s_cb_data structure that
    // is not the one supplied at registration. Work from a copy and let the
    // simulator fill obj/user_data when it has them for this reason.
    s_cb_data data = callbacks_[i];
    data.reason = reason;
    VpiApplyDispatchOverrides(data, obj, user_data);
    // §38.36.1.3: a handle to a module instance in the obj field places a
    // cbStmt callback on every statement in the module that can have one. The
    // single registration stands in for all of them, so deliver the routine
    // once per such statement - each with obj set to that statement - rather
    // than once for the module as a whole. Statements in protected portions are
    // skipped by the collector and never receive a callback.
    if (VpiIsModuleWideCbStmt(data)) {
      std::vector<VpiObject*> stmts;
      VpiCollectModuleWideStmtTargets(VpiObjectOf(data.obj), stmts);
      for (VpiObject* stmt : stmts) {
        s_cb_data per = data;
        per.obj = VpiHandleOf(stmt);
        Deliver(per);
        ++fired;
      }
      continue;
    }
    Deliver(data);
    ++fired;
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
  for (s_cb_data& slot : callbacks_) {
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
