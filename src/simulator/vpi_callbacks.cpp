#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_expr_values.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_signal_callbacks.h"
#include "simulator/vpi_user.h"
#include "simulator/vpi_value_change_watch.h"

namespace delta {

namespace {

bool IsVariableBitSelect(const VpiObject& obj) {
  return obj.type == vpiBitSelect || obj.type == vpiVarBit;
}

bool IsPlacedOnAnObject(int reason) {
  static constexpr std::array kReasons = {cbValueChange, cbSizeChange,
                                          cbStmt,        cbDisable,
                                          cbCreateObj,   cbReclaimObj};
  return std::ranges::find(kReasons, reason) != kReasons.end();
}

const char* VpiCheckCallbackPlacement(const s_cb_data& data,
                                      VpiToolPhase tool_phase) {
  if (VpiPhaseRestrictsFunctionality(tool_phase) &&
      !VpiStartupCallbackReasonAllowed(data.reason)) {
    return "vpi_register_cb() may register only an early-phase callback reason "
           "while VPI functionality is restricted";
  }

  if (IsPlacedOnAnObject(data.reason) && data.obj == nullptr) {
    return "vpi_register_cb(): a callback for this reason must be placed on an "
           "object";
  }

  if (data.reason == cbValueChange && VpiObjectOf(data.obj)->automatic) {
    return "vpi_register_cb(): a value change callback may not be placed on an "
           "automatic variable";
  }

  if ((data.reason == cbForce || data.reason == cbRelease ||
       data.reason == cbDisable) &&
      data.obj && IsVariableBitSelect(*VpiObjectOf(data.obj))) {
    return "vpi_register_cb(): a cbForce, cbRelease, or cbDisable callback may "
           "not "
           "be placed on a variable bit-select";
  }

  if (data.reason == cbStmt && VpiObjectOf(data.obj)->is_protected) {
    return "vpi_register_cb(): a cbStmt callback may not be placed on a "
           "statement "
           "in a protected portion of the code";
  }

  if (data.reason == cbStmt && VpiObjectOf(data.obj)->type != kVpiModule &&
      !VpiIsScopeBodyStmtType(VpiObjectOf(data.obj)->type)) {
    return "vpi_register_cb(): a cbStmt callback may be placed only on one of "
           "the statement objects Table 38-6 lists, or on a module instance";
  }

  return nullptr;
}

const char* VpiCheckCallbackTiming(const s_cb_data& data,
                                   bool sim_progressed_into_time_slice,
                                   int current_callback_reason,
                                   bool at_read_only_synch_time) {
  if (!VpiIsSimulationTimeCallbackReason(data.reason)) return nullptr;

  if (data.time == nullptr || data.time->type == vpiSuppressTime) {
    return "vpi_register_cb(): a simulation-time callback requires a time "
           "structure with type vpiSimTime or vpiScaledRealTime";
  }

  bool delay_is_zero =
      data.time->low == 0 && data.time->high == 0 && data.time->real == 0.0;

  if (data.reason == cbAtStartOfSimTime && delay_is_zero &&
      sim_progressed_into_time_slice &&
      current_callback_reason != cbAtStartOfSimTime) {
    return "vpi_register_cb(): a zero-delay cbAtStartOfSimTime callback may "
           "not "
           "be placed after simulation has entered a time slice, except from "
           "within a cbAtStartOfSimTime callback";
  }

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
  return type == vpiPrimTerm || type == kVpiTimeQueue || VpiIsExprType(type) ||
         VpiIsNetsType(type) || VpiIsVariablesType(type) ||
         VpiIsScopeBodyStmtType(type);
}

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
    if (GetGlobalVpiContext().CompareObjects(placed_on, ref) != 0) {
      iter->children.push_back(cb_obj);
    }
  }
}

bool HasCallbackFor(const std::vector<s_cb_data>& callbacks, int reason) {
  return std::ranges::any_of(
      callbacks, [reason](const s_cb_data& cb) { return cb.reason == reason; });
}

namespace {

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

void WatchStrengthIfAsked(const s_cb_data& data) {
  VpiObject* watched = VpiObjectOf(data.obj);
  if (watched->net != nullptr && data.value != nullptr &&
      data.value->format == vpiStrengthVal) {
    watched->net->strength_watched = true;
  }
}

bool IsCalledAsAStatementRuns(const s_cb_data& data) {
  return data.reason == cbStmt || (data.reason == cbValueChange &&
                                   VpiObjectOf(data.obj)->type == vpiEventStmt);
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

  if (data->obj != nullptr &&
      VpiIsCallbackHostType(VpiObjectOf(data->obj)->type) &&
      VpiObjectOf(data->obj)->callback == nullptr) {
    VpiObjectOf(data->obj)->callback = cb_obj;
  }
  if (data->reason == cbValueChange || data->reason == cbSizeChange) {
    WatchStrengthIfAsked(*data);
    WatchObjectChanges(*this, VpiObjectOf(data->obj));
    VpiWatchContAssignChanges(*this, VpiObjectOf(data->obj), sim_ctx_);
  }
  if (data->reason == cbSignal) VpiTrapSignal(data->index);
  if (IsCalledAsAStatementRuns(*data)) stmt_callbacks_registered_ = true;
  if (scheduler_ != nullptr &&
      VpiIsSimulationTimeCallbackReason(data->reason)) {
    ScheduleTimeCallback(*this, *scheduler_, cb_obj, *data);
  }
  return cb_obj;
}

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
  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->is_assertion_cb = true;
  cb_obj->assertion_cb_handle = placed_handle;
  cb_obj->index = -1;
  return cb_obj;
}

int VpiContext::RemoveCb(VpiHandle cb_handle) {
  if (!cb_handle) return 0;
  if (cb_handle->type != kVpiCallback) return 0;
  if (cb_handle->is_systf) return 0;
  int idx = cb_handle->index;
  if (idx >= 0 && idx < static_cast<int>(callbacks_.size())) {
    if (callbacks_[idx].reason < 0) return 0;
    const int kReason = callbacks_[idx].reason;
    callbacks_[idx].reason = -1;
    if (kReason == cbSignal)
      VpiReleaseSignal(callbacks_[idx].index, callbacks_);
    ReleaseHandle(cb_handle);
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

void VpiNormalizeSimEventCbData(s_cb_data& data) {
  if (data.reason == cbReclaimObj || data.reason == cbEndOfObject) {
    data.time = nullptr;
  }

  if (data.reason == cbValueChange &&
      (VpiObjectOf(data.obj)->type == vpiEventStmt ||
       VpiObjectOf(data.obj)->type == vpiNamedEvent ||
       VpiObjectOf(data.obj)->type == vpiClassVar)) {
    data.value = nullptr;
  }
}

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

bool VpiIsModuleWideCbStmt(const s_cb_data& data) {
  return data.reason == cbStmt && VpiObjectOf(data.obj)->type == kVpiModule;
}

bool VpiCbStmtIsPlacedOn(const s_cb_data& reg, VpiHandle stmt) {
  if (VpiObjectOf(reg.obj) == stmt) return true;
  if (VpiObjectOf(reg.obj)->type != kVpiModule) return false;
  std::vector<VpiObject*> placed;
  VpiCollectModuleWideStmtTargets(VpiObjectOf(reg.obj), placed);
  for (VpiObject* target : placed) {
    if (target == stmt) return true;
  }
  return false;
}

std::string_view ClassNameOf(const VpiObject& obj) {
  for (const VpiObject* child : obj.children) {
    if (child != nullptr && child->type == vpiClassTypespec) return child->name;
  }
  return {};
}

bool IsAboutTheObjectPlacedOn(int reason) {
  static constexpr std::array kReasons = {
      cbValueChange, cbSizeChange,  cbDisable,    cbEnterThread,
      cbEndOfFrame,  cbEndOfThread, cbEndOfObject};
  return std::ranges::find(kReasons, reason) != kReasons.end();
}

bool PlacedElsewhere(const s_cb_data& reg, int reason, VpiHandle obj) {
  if (obj == nullptr) return false;
  if (reason == cbStmt) return !VpiCbStmtIsPlacedOn(reg, obj);
  if (reg.obj == nullptr) return false;
  const VpiObject* placed = VpiObjectOf(reg.obj);
  if (IsAboutTheObjectPlacedOn(reason)) return placed != obj;
  if (reason == cbCreateObj || reason == cbReclaimObj) {
    return placed->type == vpiClassTypespec ? placed->name != ClassNameOf(*obj)
                                            : placed != obj;
  }
  return false;
}

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

void FillEventValue(s_cb_data& data, s_vpi_value& value, VpiContext& ctx,
                    VpiObject* obj) {
  if (data.reason == cbForce || data.reason == cbRelease) return;
  if (data.reason != cbValueChange && data.reason != cbSizeChange) {
    data.value = nullptr;
    return;
  }
  if (data.value == nullptr || data.value->format == vpiSuppressVal) return;
  value.format = data.value->format;
  if (data.reason == cbSizeChange) {
    value.format = vpiIntVal;
    value.value.integer = ctx.Get(vpiSize, obj);
  } else {
    ctx.GetValue(obj, &value);
  }
  data.value = &value;
}

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
  if (data.reason == cbValueChange) {
    data.index = VpiVariableIsArrayMember(obj) ? obj->index : 0;
  }
}

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

void VpiApplyDispatchOverrides(s_cb_data& data, VpiHandle obj,
                               void* user_data) {
  if (obj != nullptr) data.obj = VpiHandleOf(obj);
  if (user_data != nullptr) data.user_data = static_cast<PLI_BYTE8*>(user_data);
}

}  // namespace

void VpiContext::Deliver(s_cb_data data) {
  s_vpi_time delivered_stmt_time{};
  VpiNormalizeCbStmtData(data, delivered_stmt_time, *this);
  s_vpi_time delivered_event_time{};
  s_vpi_value delivered_value{};
  VpiFillSimEventCbData(data, delivered_event_time, delivered_value, *this);
  VpiNormalizeSimEventCbData(data);
  s_vpi_time delivered_time{};
  VpiNormalizeSimTimeCbData(data, delivered_time, *this);
  int saved_reason = current_callback_reason_;
  current_callback_reason_ = data.reason;
  EnterApplicationRoutine();
  data.cb_rtn(&data);
  LeaveApplicationRoutine();
  current_callback_reason_ = saved_reason;
}

void VpiContext::NoteThreadCreated(Process* proc) {
  if (sim_ctx_ != nullptr && HasCallbackFor(callbacks_, cbStartOfThread)) {
    ThreadObjectFor(proc);
  }
}

void VpiContext::NoteObjectCreated(ClassObject& obj) {
  if (sim_ctx_ == nullptr || !HasCallbackFor(callbacks_, cbCreateObj)) return;
  DispatchCallbacks(cbCreateObj, MadeClassObject(obj));
}

int VpiContext::DeliverCallback(VpiHandle cb_handle) {
  if (cb_handle == nullptr || cb_handle->type != kVpiCallback) return 0;
  const int kIndex = cb_handle->index;
  if (kIndex < 0 || kIndex >= static_cast<int>(callbacks_.size())) return 0;
  const s_cb_data kData = callbacks_[kIndex];
  if (kData.reason < 0 || kData.cb_rtn == nullptr) return 0;
  if (IsOneShotPliCallback(kData.reason)) callbacks_[kIndex].reason = -1;
  const bool kSavedReadOnly = at_read_only_synch_time_;
  if (kData.reason == cbReadOnlySynch) at_read_only_synch_time_ = true;
  Deliver(kData);
  at_read_only_synch_time_ = kSavedReadOnly;
  return 1;
}

int VpiContext::DispatchStrengthChange(VpiObject* obj) {
  int fired = 0;
  const size_t kCount = callbacks_.size();
  for (size_t i = 0; i < kCount; ++i) {
    const s_cb_data& reg = callbacks_[i];
    if (reg.reason != cbValueChange || reg.cb_rtn == nullptr ||
        reg.value == nullptr || reg.value->format != vpiStrengthVal ||
        PlacedElsewhere(reg, cbValueChange, obj)) {
      continue;
    }
    s_cb_data data = reg;
    VpiApplyDispatchOverrides(data, obj, nullptr);
    Deliver(data);
    ++fired;
  }
  return fired;
}

int VpiContext::DispatchCallbacks(int reason, VpiHandle obj, void* user_data) {
  int fired = 0;
  size_t count = callbacks_.size();

  for (size_t i = 0; i < count; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    if (PlacedElsewhere(callbacks_[i], reason, obj)) continue;
    if (NextSimTimeNotDue(callbacks_, cb_handles_, i, scheduler_)) continue;
    s_cb_data data = callbacks_[i];
    data.reason = reason;
    VpiApplyDispatchOverrides(data, obj, user_data);
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
  if (last_error_.level == 0) return;
  if (dispatching_error_callbacks_) return;

  dispatching_error_callbacks_ = true;
  DispatchCallbacks(last_error_.state == kVpiPLI ? kCbPLIError : kCbError);
  dispatching_error_callbacks_ = false;
}

int VpiContext::DispatchReset() {
  ClearUserDataForRestartOrReset();
  int fired = DispatchCallbacks(kCbStartOfReset);
  fired += DispatchCallbacks(kCbEndOfReset);
  return fired;
}

int VpiContext::DispatchRestart() {
  ReleaseHandlesForRestart();

  ClearUserDataForRestartOrReset();

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
  std::vector<int> precisions;
  for (const VpiObject* candidate : all_objects_) {
    if (candidate->type == kVpiModule) {
      precisions.push_back(candidate->time_precision);
    }
  }
  return VpiSmallestTimePrecision(precisions);
}

}  // namespace delta
