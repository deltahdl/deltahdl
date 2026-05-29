#include "simulator/dpi_runtime.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/sv_vpi_user.h"

namespace delta {

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
                                        DpiScope decl_scope) {
  // §35.5.3: the chain's context is the import declaration's instantiated
  // scope when SystemVerilog calls a context import.
  PushScope(std::move(decl_scope));
  call_chain_.push_back({sv_name, true});
}

void DpiRuntime::EnterNoncontextImportCall(std::string_view sv_name) {
  call_chain_.push_back({sv_name, false});
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
  const auto* exp = FindExport(sv_name);
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
