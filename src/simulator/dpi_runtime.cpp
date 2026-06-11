#include "simulator/dpi_runtime.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/sv_vpi_user.h"

namespace delta {

// §35.9 disable-protocol state for the current execution thread. A foreign
// routine queries its disabled state with no handle, so the state is naturally
// thread-local, mirroring how the C-ABI scope (g_current_scope) is held. The
// acknowledgement flag records whether svAckDisabledState() was called during
// the current disable episode; it is cleared whenever the disabled state is
// left so each episode starts unacknowledged.
namespace {
thread_local bool g_disabled_state = false;
thread_local bool g_disable_acked = false;
}  // namespace

bool DpiCurrentDisabledState() { return g_disabled_state; }

void DpiSetCurrentDisabledState(bool disabled) {
  g_disabled_state = disabled;
  // The acknowledgement is per disable episode: leaving the disabled state ends
  // the episode, so a subsequent one starts unacknowledged.
  if (!disabled) g_disable_acked = false;
}

void DpiAckCurrentDisable() { g_disable_acked = true; }

bool DpiCurrentDisableAcknowledged() { return g_disable_acked; }

DpiArgValue DpiArgValue::FromInt(int32_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kInt;
  a.data.int_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLongint(int64_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLongint;
  a.data.longint_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromReal(double v) {
  DpiArgValue a;
  a.type = DataTypeKind::kReal;
  a.data.real_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromString(std::string v) {
  DpiArgValue a;
  a.type = DataTypeKind::kString;
  a.string_val = std::move(v);
  return a;
}

DpiArgValue DpiArgValue::FromChandle(SvChandle v) {
  DpiArgValue a;
  a.type = DataTypeKind::kChandle;
  a.data.chandle_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromBit(SvBit v) {
  DpiArgValue a;
  a.type = DataTypeKind::kBit;
  a.data.bit_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogic(SvLogic v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLogic;
  a.data.logic_val = v;
  return a;
}

int32_t DpiArgValue::AsInt() const { return data.int_val; }
int64_t DpiArgValue::AsLongint() const { return data.longint_val; }
double DpiArgValue::AsReal() const { return data.real_val; }
const std::string& DpiArgValue::AsString() const { return string_val; }
SvChandle DpiArgValue::AsChandle() const { return data.chandle_val; }
SvBit DpiArgValue::AsBit() const { return data.bit_val; }
SvLogic DpiArgValue::AsLogic() const { return data.logic_val; }

void DpiRuntime::RegisterImport(DpiRtFunction func) {
  import_index_[func.sv_name] = imports_.size();
  imports_.push_back(std::move(func));
}

const DpiRtFunction* DpiRuntime::FindImport(std::string_view sv_name) const {
  auto it = import_index_.find(sv_name);
  if (it == import_index_.end()) return nullptr;
  return &imports_[it->second];
}

bool DpiRuntime::HasImport(std::string_view sv_name) const {
  return import_index_.count(sv_name) != 0;
}

uint32_t DpiRuntime::ImportCount() const {
  return static_cast<uint32_t>(imports_.size());
}

void DpiRuntime::RegisterExport(DpiRtExport exp) {
  // §35.7: exported SystemVerilog functions are always context functions.
  // Normalize the flag here so any caller that fails to set it (or sets it
  // false) still gets a context export.
  exp.is_context = true;
  export_index_[exp.sv_name] = exports_.size();
  exports_.push_back(std::move(exp));
}

const DpiRtExport* DpiRuntime::FindExport(std::string_view sv_name) const {
  auto it = export_index_.find(sv_name);
  if (it == export_index_.end()) return nullptr;
  return &exports_[it->second];
}

bool DpiRuntime::HasExport(std::string_view sv_name) const {
  return export_index_.count(sv_name) != 0;
}

uint32_t DpiRuntime::ExportCount() const {
  return static_cast<uint32_t>(exports_.size());
}

DpiArgValue DpiRuntime::CallImport(std::string_view sv_name,
                                   const std::vector<DpiArgValue>& args) const {
  const auto* func = FindImport(sv_name);
  if (!func || !func->impl) return DpiArgValue::FromInt(0);
  return func->impl(args);
}

DpiArgValue DpiRuntime::UndeterminedOutputValue(DataTypeKind type) {
  // §35.5.1.2: the initial value of an output argument is undetermined and
  // implementation dependent. We pick a deterministic per-type zero so the
  // callee observes a value that is independent of the caller's actual.
  switch (type) {
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return DpiArgValue::FromLongint(0);
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return DpiArgValue::FromReal(0.0);
    case DataTypeKind::kString:
      return DpiArgValue::FromString("");
    case DataTypeKind::kChandle:
      return DpiArgValue::FromChandle(nullptr);
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(0);
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return DpiArgValue::FromLogic(0);
    default:
      return DpiArgValue::FromInt(0);
  }
}

DpiArgValue DpiRuntime::CallImportWithArgs(
    std::string_view sv_name, std::vector<DpiArgValue>& actuals) const {
  const auto* func = FindImport(sv_name);
  if (!func) return DpiArgValue::FromInt(0);

  // The vector the foreign function operates on. Input and inout arguments are
  // seeded with the caller's actual value, so the foreign function can read an
  // inout argument's initial value. An output argument is seeded with an
  // undetermined value instead of the actual, because the foreign function
  // shall not assume anything about an output argument's initial value.
  std::vector<DpiArgValue> callee = actuals;
  for (size_t i = 0; i < func->args.size() && i < callee.size(); ++i) {
    if (func->args[i].direction == Direction::kOutput) {
      callee[i] = UndeterminedOutputValue(func->args[i].type);
    }
  }

  DpiArgValue result = DpiArgValue::FromInt(0);
  if (func->arg_impl) {
    result = func->arg_impl(callee);
  } else if (func->impl) {
    result = func->impl(callee);
  }

  // §35.9: when a disable is in effect, the values of an imported subroutine's
  // output and inout parameters are undefined, as is its return value. A
  // SystemVerilog simulator is not obligated to propagate anything the foreign
  // code wrote back to the calling SystemVerilog code. This implementation
  // exercises that latitude: the actuals are left untouched and an undetermined
  // result of the return type is yielded, so no disabled-call value leaks out.
  if (DpiCurrentDisabledState()) {
    return UndeterminedOutputValue(func->return_type);
  }

  // Copy back only output and inout arguments: the value the foreign function
  // wrote to them is visible outside the call. Input arguments are passed by
  // value, so any modification the foreign function made to its copy is
  // discarded here and the caller's actual is left unchanged.
  for (size_t i = 0; i < func->args.size() && i < actuals.size(); ++i) {
    Direction dir = func->args[i].direction;
    if (dir == Direction::kOutput || dir == Direction::kInout) {
      actuals[i] = callee[i];
    }
  }
  return result;
}

DpiArgValue DpiRuntime::CallExport(std::string_view sv_name,
                                   const std::vector<DpiArgValue>& args) const {
  const auto* exp = FindExport(sv_name);
  if (!exp || !exp->impl) return DpiArgValue::FromInt(0);
  return exp->impl(args);
}

void DpiRuntime::PushScope(DpiScope scope) {
  scope_stack_.push_back(std::move(scope));
  current_scope_ = &scope_stack_.back();
}

void DpiRuntime::PopScope() {
  if (scope_stack_.empty()) return;
  scope_stack_.pop_back();
  current_scope_ = scope_stack_.empty() ? nullptr : &scope_stack_.back();
}

const DpiScope* DpiRuntime::CurrentScope() const { return current_scope_; }

void DpiRuntime::SetScope(const DpiScope* scope) { current_scope_ = scope; }

const DpiScope* DpiRuntime::GetScope() const { return current_scope_; }

uint32_t DpiRuntime::SvLow(const SvOpenArrayHandle&) { return 0; }

uint32_t DpiRuntime::SvHigh(const SvOpenArrayHandle& h) {
  return h.size > 0 ? h.size - 1 : 0;
}

uint32_t DpiRuntime::SvSize(const SvOpenArrayHandle& h) { return h.size; }

void DpiRuntime::EnterContextImportCall(std::string_view sv_name,
                                        DpiScope decl_scope, bool is_task) {
  // §35.5.3: the chain's context is the import declaration's instantiated
  // scope when SystemVerilog calls a context import.
  PushScope(std::move(decl_scope));
  call_chain_.push_back({sv_name, true, is_task});
}

void DpiRuntime::EnterNoncontextImportCall(std::string_view sv_name,
                                           bool is_task) {
  call_chain_.push_back({sv_name, false, is_task});
}

void DpiRuntime::LeaveImportCall() {
  if (call_chain_.empty()) return;
  bool had_context = call_chain_.back().is_context;
  call_chain_.pop_back();
  if (had_context) PopScope();
}

uint32_t DpiRuntime::ImportCallDepth() const {
  return static_cast<uint32_t>(call_chain_.size());
}

bool DpiRuntime::ChainRootIsContext() const {
  if (call_chain_.empty()) return false;
  // §35.5.3: context property attaches to the *root* of the import chain,
  // never transitively promoted to subsequent inner calls.
  return call_chain_.front().is_context;
}

DpiExportCallStatus DpiRuntime::CallExportFromImport(
    std::string_view sv_name, const std::vector<DpiArgValue>& args,
    DpiArgValue* out_result) {
  const auto* exp = FindExport(sv_name);
  // §35.9 item d): once an imported subroutine has entered the disabled state,
  // it is illegal for the current call to make any further calls to exported
  // subroutines. This applies whatever the chain's context property or the kind
  // of export, so it is checked ahead of the §35.8 and §35.5.3 rules.
  if (DpiCurrentDisabledState()) {
    return DpiExportCallStatus::kDisabledStateExportCall;
  }
  // §35.8: it is never legal to call an exported task from within an imported
  // function — the DPI counterpart of the native rule that a function cannot
  // perform a task enable. When the innermost import in the chain is a function
  // and the export it is invoking names a task, reject the call outright,
  // independent of the chain's context property.
  if (!call_chain_.empty() && !call_chain_.back().is_task && exp != nullptr &&
      exp->is_task) {
    return DpiExportCallStatus::kFunctionCallsTask;
  }
  // §35.5.3: a noncontext DPI subroutine cannot call a SystemVerilog export.
  // The check looks at the *current* (innermost) import call's context
  // property, not the chain root, because context is not transitively
  // promoted.
  if (call_chain_.empty() || !call_chain_.back().is_context) {
    return DpiExportCallStatus::kNoncontextChain;
  }
  // §35.5.3: only exports declared in the chain's current scope can be
  // invoked directly. Calling an export defined in a different scope
  // requires the import to first set the chain scope via svSetScope.
  // When the export's scope_name is empty we treat the export as
  // scope-agnostic to keep callers that don't record scopes working.
  if (exp != nullptr && !exp->scope_name.empty() && current_scope_ != nullptr &&
      exp->scope_name != current_scope_->name) {
    return DpiExportCallStatus::kScopeMismatch;
  }
  // §35.5.3: when the export call returns, the chain context shall be the
  // value it had at the point the export was invoked. Snapshot and restore
  // around the call so that any scope changes performed by the export (or
  // by code it called) do not leak back to the import chain.
  const DpiScope* saved_scope = current_scope_;
  DpiArgValue result = CallExport(sv_name, args);
  current_scope_ = saved_scope;
  if (out_result) *out_result = result;
  return DpiExportCallStatus::kOk;
}

bool DpiRuntime::IsImportCallOptimizationBarrier(
    std::string_view sv_name) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr) return false;
  return func->is_context;
}

int DpiRuntime::ReturnFromExportUnderDisable(DpiDisableTarget target) {
  switch (target) {
    case DpiDisableTarget::kAncestor:
      // §35.9 item a): the exported task returns because a disable targets a
      // parent. The disable is still propagating, so the calling import enters
      // the disabled state and the task returns 1.
      DpiSetCurrentDisabledState(true);
      return 1;
    case DpiDisableTarget::kExportItself:
      // §35.9: when the exported task is itself the disable target, the disable
      // stops there — its parent import is not considered disabled, the task
      // returns 0, and svIsDisabledState() reports 0.
      DpiSetCurrentDisabledState(false);
      return 0;
    case DpiDisableTarget::kNone:
    default:
      // §35.9 item a): a task that does not return due to a disable returns 0.
      DpiSetCurrentDisabledState(false);
      return 0;
  }
}

bool DpiRuntime::IsDisabledState() const { return DpiCurrentDisabledState(); }

bool DpiRuntime::CheckImportedSubroutineDisableReturn(
    bool is_task, int task_return_value) const {
  // §35.9: the verification only applies to a subroutine returning while a
  // disable is in effect. With no disable there is nothing to check.
  if (!DpiCurrentDisabledState()) return true;
  if (is_task) {
    // item b): an imported task returning due to a disable shall return 1.
    return task_return_value == 1;
  }
  // item c): an imported function returning due to a disable shall have
  // acknowledged it by calling svAckDisabledState() first.
  return DpiCurrentDisableAcknowledged();
}

void AssertionApi::RegisterCallback(int reason, AssertionCbFunc cb,
                                    void* user_data) {
  callbacks_.push_back({reason, std::move(cb), user_data});
}

void AssertionApi::FireCallback(const AssertionCbData& data) {
  for (auto& entry : callbacks_) {
    if (entry.reason == data.reason) {
      entry.cb(data);
    }
  }
}

uint32_t AssertionApi::CallbackCount() const {
  return static_cast<uint32_t>(callbacks_.size());
}

namespace {

// §39.4.2: the step callbacks. A single placed step callback covers both, so
// matching treats the two step reasons interchangeably.
bool IsStepReason(int reason) {
  return reason == cbAssertionStepSuccess || reason == cbAssertionStepFailure;
}

}  // namespace

bool AssertionApi::IsAssertionCallbackReason(int reason) {
  switch (reason) {
    case cbAssertionStart:
    case cbAssertionSuccess:
    case cbAssertionVacuousSuccess:
    case cbAssertionDisabledEvaluation:
    case cbAssertionFailure:
    case cbAssertionStepSuccess:
    case cbAssertionStepFailure:
    case cbAssertionLock:
    case cbAssertionUnlock:
    case cbAssertionDisable:
    case cbAssertionEnable:
    case cbAssertionReset:
    case cbAssertionKill:
    case cbAssertionDisablePassAction:
    case cbAssertionEnablePassAction:
    case cbAssertionDisableFailAction:
    case cbAssertionEnableFailAction:
    case cbAssertionDisableVacuousAction:
    case cbAssertionEnableNonvacuousAction:
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsAssertionSysCallbackReason(int reason) {
  switch (reason) {
    case cbAssertionSysInitialized:
    case cbAssertionSysLock:
    case cbAssertionSysUnlock:
    case cbAssertionSysOn:
    case cbAssertionSysOff:
    case cbAssertionSysKill:
    case cbAssertionSysEnd:
    case cbAssertionSysReset:
    case cbAssertionSysEnablePassAction:
    case cbAssertionSysEnableFailAction:
    case cbAssertionSysDisablePassAction:
    case cbAssertionSysDisableFailAction:
    case cbAssertionSysEnableNonvacuousAction:
    case cbAssertionSysDisableVacuousAction:
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsReasonValidForHandle(int reason, int handle_type) {
  if (!IsAssertionCallbackReason(reason)) return false;
  // Any assertion callback reason may be placed on a concurrent or immediate
  // assertion statement.
  if (IsAssertionStatementHandle(handle_type)) return true;
  // A sequence or property instance accepts only the start, success, and
  // failure callbacks.
  if (handle_type == vpiSequenceDecl || handle_type == vpiProperty ||
      handle_type == vpiPropertyDecl) {
    return reason == cbAssertionStart || reason == cbAssertionSuccess ||
           reason == cbAssertionFailure;
  }
  // No other handle type bears assertion callbacks.
  return false;
}

bool AssertionApi::ReasonCarriesAttemptInfo(int reason) {
  switch (reason) {
    // The control and action callbacks carry no attempt information.
    case cbAssertionLock:
    case cbAssertionUnlock:
    case cbAssertionDisable:
    case cbAssertionEnable:
    case cbAssertionReset:
    case cbAssertionKill:
    case cbAssertionDisablePassAction:
    case cbAssertionEnablePassAction:
    case cbAssertionDisableFailAction:
    case cbAssertionEnableFailAction:
    case cbAssertionDisableVacuousAction:
    case cbAssertionEnableNonvacuousAction:
      return false;
    default:
      return true;
  }
}

bool AssertionApi::IsValidFailingStep(const AssertionStepDetail& step) {
  return !step.matched_exprs.empty();
}

AssertionCallbackHandle AssertionApi::PlaceAssertionCallback(
    int reason, std::string_view assertion, int handle_type,
    AssertionPlacedCallback cb, void* user_data) {
  // An empty (null) handle, an unknown reason, or a reason that may not be
  // placed on this handle type is a placement error: return the NULL handle.
  if (assertion.empty()) return 0;
  if (!IsReasonValidForHandle(reason, handle_type)) return 0;

  AssertionCallbackHandle handle = next_callback_handle_++;
  placed_callbacks_.push_back(
      {handle, reason, std::string(assertion), std::move(cb), user_data});
  return handle;
}

bool AssertionApi::RemoveAssertionCallback(AssertionCallbackHandle handle) {
  if (handle == 0) return false;
  auto before = placed_callbacks_.size();
  std::erase_if(placed_callbacks_,
                [handle](const PlacedCb& e) { return e.handle == handle; });
  return placed_callbacks_.size() != before;
}

uint32_t AssertionApi::PlacedCallbackCount() const {
  return static_cast<uint32_t>(placed_callbacks_.size());
}

uint32_t AssertionApi::DeliverAssertionEvent(std::string_view assertion,
                                             int reason, uint64_t cb_time,
                                             const AssertionAttemptInfo& info) {
  // A failing step shall always carry at least one expression; a malformed one
  // is rejected and fires nothing.
  if (reason == cbAssertionStepFailure && !IsValidFailingStep(info.step)) {
    return 0;
  }

  AssertionCallbackArgs args;
  args.reason = reason;
  args.cb_time = cb_time;
  args.assertion = std::string(assertion);
  args.user_data = nullptr;
  // The attempt-info pointer is null for the reasons that carry no attempt
  // information; otherwise it points at the supplied attempt information.
  const AssertionAttemptInfo* info_ptr =
      ReasonCarriesAttemptInfo(reason) ? &info : nullptr;
  args.info = info_ptr;

  uint32_t fired = 0;
  for (auto& entry : placed_callbacks_) {
    if (std::string_view(entry.assertion) != assertion) continue;
    // A placed step callback is invoked for both success and failure steps;
    // every other reason matches exactly.
    bool matches = IsStepReason(entry.reason) ? IsStepReason(reason)
                                              : entry.reason == reason;
    if (!matches) continue;
    args.user_data = entry.user_data;
    entry.cb(args);
    ++fired;
  }
  return fired;
}

void AssertionApi::SetSeverity(std::string_view name, AssertionSeverity sev) {
  severity_map_[std::string(name)] = sev;
}

AssertionSeverity AssertionApi::GetSeverity(std::string_view name) const {
  auto it = severity_map_.find(std::string(name));
  if (it == severity_map_.end()) return AssertionSeverity::kError;
  return it->second;
}

void AssertionApi::SetAction(std::string_view name, AssertionAction action) {
  action_map_[std::string(name)] = action;
}

AssertionAction AssertionApi::GetAction(std::string_view name) const {
  auto it = action_map_.find(std::string(name));
  if (it == action_map_.end()) return AssertionAction::kNone;
  return it->second;
}

bool AssertionApi::SysControl(int control, std::string_view scope) {
  // Once the system has ended, no further assertion-related actions are
  // permitted.
  if (ended_) return false;
  // While locked, the status of the assertions cannot be changed; only an
  // unlock control may proceed.
  if (locked_ && control != vpiAssertionSysUnlock) return false;

  // An empty (null) scope means the control applies to all assertions
  // regardless of scope.
  last_control_global_ = scope.empty();

  switch (control) {
    case vpiAssertionSysReset:
      // Discard attempts in progress and restore the system to its initial
      // state. Step success/failure callbacks are removed; all others remain.
      attempts_in_progress_ = 0;
      started_ = true;
      fail_action_enabled_ = true;
      vacuous_action_enabled_ = true;
      nonvacuous_action_enabled_ = true;
      std::erase_if(callbacks_, [](const CbEntry& e) {
        return e.reason == cbAssertionStepSuccess ||
               e.reason == cbAssertionStepFailure;
      });
      return true;
    case vpiAssertionSysOff:
      // Disable further starts; attempts already executing are not affected.
      started_ = false;
      return true;
    case vpiAssertionSysKill:
      // Discard attempts in progress and disable further starts.
      attempts_in_progress_ = 0;
      started_ = false;
      return true;
    case vpiAssertionSysLock:
      locked_ = true;
      return true;
    case vpiAssertionSysUnlock:
      locked_ = false;
      return true;
    case vpiAssertionSysOn:
      // Restart the system so attempts resume on all assertions.
      started_ = true;
      return true;
    case vpiAssertionSysEnd:
      // Discard attempts, disable further starts, remove all installed
      // callbacks, and permit no further actions.
      attempts_in_progress_ = 0;
      started_ = false;
      ended_ = true;
      callbacks_.clear();
      return true;
    case vpiAssertionSysDisablePassAction:
      vacuous_action_enabled_ = false;
      nonvacuous_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnablePassAction:
      vacuous_action_enabled_ = true;
      nonvacuous_action_enabled_ = true;
      return true;
    case vpiAssertionSysDisableFailAction:
      fail_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnableFailAction:
      fail_action_enabled_ = true;
      return true;
    case vpiAssertionSysDisableVacuousAction:
      vacuous_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnableNonvacuousAction:
      nonvacuous_action_enabled_ = true;
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsAssertionStatementHandle(int vpi_type) {
  // Assert/assume/cover statements (immediate or concurrent) are the only
  // handles these per-assertion controls accept. Sequence and property
  // instances are not valid targets.
  switch (vpi_type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
    case vpiImmediateAssert:
    case vpiImmediateAssume:
    case vpiImmediateCover:
      return true;
    default:
      return false;
  }
}

AssertionApi::AssertionControlState& AssertionApi::StateFor(
    std::string_view assertion) {
  return assertion_state_[std::string(assertion)];
}

const AssertionApi::AssertionControlState* AssertionApi::FindState(
    std::string_view assertion) const {
  auto it = assertion_state_.find(std::string(assertion));
  return it == assertion_state_.end() ? nullptr : &it->second;
}

bool AssertionApi::Control(int control, std::string_view assertion) {
  // The second argument shall be a valid assertion handle.
  if (assertion.empty()) return false;
  AssertionControlState& s = StateFor(assertion);
  // While locked, the status of the assertion cannot be changed without first
  // unlocking it.
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionReset:
      // Discard all attempts in progress for this assertion (which also clears
      // their per-attempt stepping) and restore it to its initial state.
      s.attempts.clear();
      s.enabled = true;
      s.fail_action_enabled = true;
      s.vacuous_action_enabled = true;
      s.nonvacuous_action_enabled = true;
      return true;
    case vpiAssertionLock:
      s.locked = true;
      return true;
    case vpiAssertionUnlock:
      s.locked = false;
      return true;
    case vpiAssertionDisable:
      // Disable the starting of new attempts; existing attempts are unaffected.
      s.enabled = false;
      return true;
    case vpiAssertionEnable:
      s.enabled = true;
      return true;
    case vpiAssertionDisablePassAction:
      // Pass action covers both vacuous and nonvacuous success.
      s.vacuous_action_enabled = false;
      s.nonvacuous_action_enabled = false;
      return true;
    case vpiAssertionEnablePassAction:
      s.vacuous_action_enabled = true;
      s.nonvacuous_action_enabled = true;
      return true;
    case vpiAssertionDisableFailAction:
      s.fail_action_enabled = false;
      return true;
    case vpiAssertionEnableFailAction:
      s.fail_action_enabled = true;
      return true;
    case vpiAssertionDisableVacuousAction:
      s.vacuous_action_enabled = false;
      return true;
    case vpiAssertionEnableNonvacuousAction:
      s.nonvacuous_action_enabled = true;
      return true;
    default:
      return false;
  }
}

bool AssertionApi::ControlAttempt(int control, std::string_view assertion,
                                  uint64_t attempt_start_time) {
  if (assertion.empty()) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionKill:
      // Discard the given attempt (identified by its start time); the assertion
      // stays enabled and no state used by it (e.g., past() sampling) is reset.
      s.attempts.erase(attempt_start_time);
      return true;
    case vpiAssertionDisableStep: {
      // Disable step callbacks for the given attempt; no effect (idempotent)
      // when that attempt is not stepping or has no entry.
      auto it = s.attempts.find(attempt_start_time);
      if (it != s.attempts.end()) it->second.step_enabled = false;
      return true;
    }
    default:
      return false;
  }
}

bool AssertionApi::ControlStep(int control, std::string_view assertion,
                               uint64_t attempt_start_time, int step_control) {
  if (assertion.empty()) return false;
  // The fourth argument shall be a step control constant.
  if (step_control != vpiAssertionClockSteps) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionEnableStep: {
      // Enable step callbacks for the given assertion attempt; stepping is
      // disabled by default for every attempt. The stepping mode can only be
      // set before the attempt has started: once it is in progress its mode is
      // frozen, so a later enable is accepted but has no effect.
      AttemptControlState& att = s.attempts[attempt_start_time];
      if (!att.started) att.step_enabled = true;
      return true;
    }
    default:
      return false;
  }
}

bool AssertionApi::AssertionEnabled(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->enabled : true;
}

bool AssertionApi::AssertionLocked(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->locked : false;
}

bool AssertionApi::AssertionPassActionEnabled(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return true;
  return s->vacuous_action_enabled && s->nonvacuous_action_enabled;
}

bool AssertionApi::AssertionFailActionEnabled(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->fail_action_enabled : true;
}

bool AssertionApi::AssertionVacuousActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->vacuous_action_enabled : true;
}

bool AssertionApi::AssertionNonvacuousActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->nonvacuous_action_enabled : true;
}

bool AssertionApi::AssertionStepEnabled(std::string_view assertion,
                                        uint64_t attempt_start_time) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return false;
  auto it = s->attempts.find(attempt_start_time);
  return it != s->attempts.end() && it->second.step_enabled;
}

uint32_t AssertionApi::AssertionAttemptsInProgress(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return 0;
  // Only attempts that have actually started count as in progress; an entry may
  // exist solely to hold a pre-start stepping configuration.
  uint32_t count = 0;
  for (const auto& [time, att] : s->attempts) {
    if (att.started) ++count;
  }
  return count;
}

void AssertionApi::NoteAssertionAttemptStarted(std::string_view assertion,
                                               uint64_t attempt_start_time) {
  if (assertion.empty()) return;
  // Mark the attempt started, preserving any stepping enabled for it ahead of
  // time. A brand-new entry has stepping disabled by default.
  StateFor(assertion).attempts[attempt_start_time].started = true;
}

void CoverageApi::SetControl(CoverageControl ctrl) { control_ = ctrl; }
CoverageControl CoverageApi::GetControl() const { return control_; }

void CoverageApi::SetMaxBins(uint32_t max_bins) { max_bins_ = max_bins; }
uint32_t CoverageApi::GetMaxBins() const { return max_bins_; }

void CoverageApi::SetActive(bool active) { active_ = active; }
bool CoverageApi::IsActive() const { return active_; }

void CoverageApi::StoreValue(std::string_view key, double value) {
  values_[std::string(key)] = value;
}

double CoverageApi::GetValue(std::string_view key) const {
  auto it = values_.find(std::string(key));
  if (it == values_.end()) return 0.0;
  return it->second;
}

void DataReadApi::StoreVariable(std::string_view name,
                                const DataReadValue& val) {
  variables_[std::string(name)] = val;
}

DataReadValue DataReadApi::GetValue(std::string_view name,
                                    DataReadFormat fmt) const {
  auto it = variables_.find(std::string(name));
  if (it == variables_.end()) return DataReadValue{fmt, 0, 0.0, "", 0, {}};
  DataReadValue result = it->second;
  result.format = fmt;
  return result;
}

void DataReadApi::PutValue(std::string_view name, const DataReadValue& val) {
  variables_[std::string(name)] = val;
  NotifyValueChange(name, val);
}

void DataReadApi::RegisterValueChangeCb(std::string_view name,
                                        ValueChangeCb cb) {
  change_cbs_[std::string(name)].push_back(std::move(cb));
}

void DataReadApi::NotifyValueChange(std::string_view name,
                                    const DataReadValue& val) {
  auto it = change_cbs_.find(std::string(name));
  if (it == change_cbs_.end()) return;
  for (auto& cb : it->second) {
    cb(name, val);
  }
}

uint32_t DataReadApi::ValueChangeCbCount() const {
  uint32_t total = 0;
  for (const auto& [key, cbs] : change_cbs_) {
    total += static_cast<uint32_t>(cbs.size());
  }
  return total;
}

}  // namespace delta
