#include "simulator/vpi.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

#include "simulator/vpi_internal.h"

namespace delta {

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;

  // §36.10.2: while VPI functionality is restricted - the startup phase, and
  // the sizetf phase after it that permits no additional access - a callback
  // may be registered only for the six early-phase reasons. Reject any other
  // reason rather than register a callback the phase does not allow.
  if (VpiPhaseRestrictsFunctionality(tool_phase_) &&
      !VpiStartupCallbackReasonAllowed(data->reason)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb() may register only an early-phase callback reason "
        "while VPI functionality is restricted";
    return nullptr;
  }

  // §37.43 detail 2: it is illegal to place a value change callback on an
  // automatic variable - automatic storage exists only while its frame is
  // active, so there is no persistent object to watch. Reject the registration.
  if (data->reason == cbValueChange && data->obj && data->obj->automatic) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb(): a value change callback may not be placed on an "
        "automatic variable";
    return nullptr;
  }

  // §38.36.1: it is illegal to place a cbForce, cbRelease, or cbDisable
  // simulation-event callback on a variable bit-select. A single addressed bit
  // of a variable is not a legal target for a force/release/disable callback,
  // so reject the registration instead of handing back a callback that could
  // never fire correctly.
  if ((data->reason == cbForce || data->reason == cbRelease ||
       data->reason == cbDisable) &&
      data->obj && data->obj->type == vpiBitSelect) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb(): a cbForce, cbRelease, or cbDisable callback may "
        "not "
        "be placed on a variable bit-select";
    return nullptr;
  }

  // §38.36.1.1: placing a cbStmt callback on a statement that resides in a
  // protected portion of the code is not allowed. Such a statement is sealed
  // behind encryption, so a per-statement callback cannot be placed on it;
  // reject the registration with a null handle and a recorded error message.
  if (data->reason == cbStmt && data->obj && data->obj->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb(): a cbStmt callback may not be placed on a statement "
        "in a protected portion of the code";
    return nullptr;
  }

  // §38.36.2: a simulation-time callback carries its timing in the s_cb_data
  // time structure, and the standard constrains how that structure - and a
  // delay of zero - may be used. These checks apply only to the time-related
  // reasons; every other reason ignores the time field.
  if (VpiIsSimulationTimeCallbackReason(data->reason)) {
    // §38.36.2: the time->type field shall be vpiSimTime or vpiScaledRealTime.
    // A vpiSuppressTime type, or a null time pointer, leaves no time for the
    // callback to fire at, so registration is an error and no callback is made.
    if (data->time == nullptr || data->time->type == vpiSuppressTime) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a simulation-time callback requires a time "
          "structure with type vpiSimTime or vpiScaledRealTime";
      return nullptr;
    }

    // §38.36.2: the requested time, or the delay before the callback, lives in
    // time->{low,high,real}; a delay of zero is all three being zero.
    bool delay_is_zero = data->time->low == 0 && data->time->high == 0 &&
                         data->time->real == 0.0;

    // §38.36.2: a zero-delay cbAtStartOfSimTime callback may not be placed once
    // simulation has progressed into a time slice - unless the application is
    // itself running inside a cbAtStartOfSimTime callback, where it is allowed
    // and produces another cbAtStartOfSimTime callback in the same time slice.
    if (data->reason == cbAtStartOfSimTime && delay_is_zero &&
        sim_progressed_into_time_slice_ &&
        current_callback_reason_ != cbAtStartOfSimTime) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a zero-delay cbAtStartOfSimTime callback may not "
          "be placed after simulation has entered a time slice, except from "
          "within a cbAtStartOfSimTime callback";
      return nullptr;
    }

    // §38.36.2: a zero-delay cbReadWriteSynch callback may not be placed at
    // read-only synch time, where scheduling an event for the current time is
    // not permitted.
    if (data->reason == cbReadWriteSynch && delay_is_zero &&
        at_read_only_synch_time_) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a zero-delay cbReadWriteSynch callback may not "
          "be "
          "placed at read-only synch time";
      return nullptr;
    }
  }

  callbacks_.push_back(*data);

  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->index = static_cast<int>(callbacks_.size() - 1);
  cb_handles_.push_back(cb_obj);
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
    // §38.36.1.1: the s_cb_data delivered for a cbStmt callback has fixed
    // contents regardless of what was supplied at registration - the value
    // field is always NULL and the index field is always 0. In addition, when
    // the callback was registered with a vpiSuppressTime time type, no time is
    // passed to the routine and the time pointer is set to NULL.
    if (data.reason == cbStmt) {
      data.value = nullptr;
      data.index = 0;
      if (data.time != nullptr && data.time->type == vpiSuppressTime) {
        data.time = nullptr;
      }
    }
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
    if (data.reason == cbStmt && data.obj != nullptr &&
        data.obj->type == kVpiModule) {
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
