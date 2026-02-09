#include "simulation/dpi_runtime.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

// =============================================================================
// DpiArgValue factory methods
// =============================================================================

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

DpiArgValue DpiArgValue::FromChandle(svChandle v) {
  DpiArgValue a;
  a.type = DataTypeKind::kChandle;
  a.data.chandle_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromBit(svBit v) {
  DpiArgValue a;
  a.type = DataTypeKind::kBit;
  a.data.bit_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogic(svLogic v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLogic;
  a.data.logic_val = v;
  return a;
}

int32_t DpiArgValue::AsInt() const { return data.int_val; }
int64_t DpiArgValue::AsLongint() const { return data.longint_val; }
double DpiArgValue::AsReal() const { return data.real_val; }
const std::string& DpiArgValue::AsString() const { return string_val; }
svChandle DpiArgValue::AsChandle() const { return data.chandle_val; }
svBit DpiArgValue::AsBit() const { return data.bit_val; }
svLogic DpiArgValue::AsLogic() const { return data.logic_val; }

// =============================================================================
// DpiRuntime: import management
// =============================================================================

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

// =============================================================================
// DpiRuntime: export management
// =============================================================================

void DpiRuntime::RegisterExport(DpiRtExport exp) {
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

// =============================================================================
// DpiRuntime: function calls
// =============================================================================

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

// =============================================================================
// DpiRuntime: scope management
// =============================================================================

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

// =============================================================================
// DpiRuntime: open array support
// =============================================================================

uint32_t DpiRuntime::SvLow(const svOpenArrayHandle& /*h*/) { return 0; }

uint32_t DpiRuntime::SvHigh(const svOpenArrayHandle& h) {
  return h.size > 0 ? h.size - 1 : 0;
}

uint32_t DpiRuntime::SvSize(const svOpenArrayHandle& h) { return h.size; }

// =============================================================================
// AssertionApi
// =============================================================================

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

// =============================================================================
// CoverageApi
// =============================================================================

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

// =============================================================================
// DataReadApi
// =============================================================================

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
