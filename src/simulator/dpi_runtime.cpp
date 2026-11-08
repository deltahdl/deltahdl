#include "simulator/dpi_runtime.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/assertion_api.h"
#include "simulator/coverage_control.h"
#include "simulator/dpi_arg_value.h"

namespace delta {

namespace {
thread_local bool g_disabled_state = false;
thread_local bool g_disable_acked = false;
}  // namespace

bool DpiCurrentDisabledState() { return g_disabled_state; }

void DpiSetCurrentDisabledState(bool disabled) {
  g_disabled_state = disabled;
  if (!disabled) g_disable_acked = false;
}

void DpiAckCurrentDisable() { g_disable_acked = true; }

bool DpiCurrentDisableAcknowledged() { return g_disable_acked; }

DpiCompatibilityLevel DpiCompatibilityLevelOf(std::string_view sv_dpi_version) {
  return sv_dpi_version == "SV3.1a" ? DpiCompatibilityLevel::kSv31a
                                    : DpiCompatibilityLevel::kIeee1800;
}

bool DpiOpaqueHandlesAreRequiredForAllPackedArguments(
    DpiCompatibilityLevel level) {
  return level == DpiCompatibilityLevel::kSv31a;
}

DpiPackedArgPassing DpiPassingSemanticsOfSpecString(
    std::string_view dpi_spec_string) {
  return dpi_spec_string == "DPI" ? DpiPackedArgPassing::kSv31aReference
                                  : DpiPackedArgPassing::kCanonical;
}

bool DpiSv31aDefinitionsAreObligatoryInSvdpiH() { return false; }

bool DpiCCodeMayFailToBind(bool implementation_supports_sv31a_functionality) {
  return !implementation_supports_sv31a_functionality;
}

DpiApplicationCompatibility DpiCompatibilityOfApplication(bool uses_svdpi_src) {
  return uses_svdpi_src ? DpiApplicationCompatibility::kSource
                        : DpiApplicationCompatibility::kBinary;
}

bool DpiApplicationIsRecompiledPerSimulator(bool uses_svdpi_src) {
  return uses_svdpi_src;
}

uint32_t DpiSvdpiSrcSymbolCount() { return 2; }

bool DpiPackedArrayMacroMayDefineAnArrayType() { return false; }

bool DpiSvdpiSrcIsNeededForExportCall(
    bool allocates_representation_dynamically) {
  return !allocates_representation_dynamically;
}

namespace {

int64_t NumericToInt(const DpiArgValue& v) {
  switch (v.type) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return static_cast<int64_t>(std::llround(v.AsReal()));
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return v.AsLongint();
    case DataTypeKind::kBit:
      return v.AsBit();
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return v.AsLogic();
    case DataTypeKind::kInteger:
      return static_cast<int32_t>(v.AsLogicVec().aval);
    default:
      return v.AsInt();
  }
}

double NumericToReal(const DpiArgValue& v) {
  switch (v.type) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return v.AsReal();
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return static_cast<double>(v.AsLongint());
    case DataTypeKind::kBit:
      return static_cast<double>(v.AsBit());
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return static_cast<double>(v.AsLogic());
    case DataTypeKind::kInteger:
      return static_cast<double>(static_cast<int32_t>(v.AsLogicVec().aval));
    default:
      return static_cast<double>(v.AsInt());
  }
}

bool SameArgValue(const DpiArgValue& a, const DpiArgValue& b) {
  if (a.type != b.type) return false;
  if (a.IsArray() || b.IsArray()) {
    return std::equal(a.elements.begin(), a.elements.end(), b.elements.begin(),
                      b.elements.end(), SameArgValue);
  }
  if (a.IsWideVec() || b.IsWideVec()) {
    return a.VecWidth() == b.VecWidth() &&
           std::equal(a.AsLogicVecWords().begin(), a.AsLogicVecWords().end(),
                      b.AsLogicVecWords().begin(), b.AsLogicVecWords().end(),
                      [](SvLogicVecVal x, SvLogicVecVal y) {
                        return x.aval == y.aval && x.bval == y.bval;
                      });
  }
  switch (a.type) {
    case DataTypeKind::kInteger:
      return a.AsLogicVec().aval == b.AsLogicVec().aval &&
             a.AsLogicVec().bval == b.AsLogicVec().bval;
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return a.AsReal() == b.AsReal();
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return a.AsLongint() == b.AsLongint();
    case DataTypeKind::kString:
      return a.AsString() == b.AsString();
    case DataTypeKind::kChandle:
      return a.AsChandle() == b.AsChandle();
    case DataTypeKind::kBit:
      return a.AsBit() == b.AsBit();
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return a.AsLogic() == b.AsLogic();
    default:
      return a.AsInt() == b.AsInt();
  }
}

}  // namespace

DpiArgValue CoerceArgValue(const DpiArgValue& v, DataTypeKind target) {
  if (v.IsWideVec()) return v;
  if (v.type == target) return v;
  switch (target) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime: {
      DpiArgValue r = DpiArgValue::FromReal(NumericToReal(v));
      r.type = target;
      return r;
    }
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime: {
      DpiArgValue r = DpiArgValue::FromLongint(NumericToInt(v));
      r.type = target;
      return r;
    }
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(static_cast<SvBit>(NumericToInt(v) & 1));
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg: {
      DpiArgValue r =
          DpiArgValue::FromLogic(static_cast<SvLogic>(NumericToInt(v) & 1));
      r.type = target;
      return r;
    }
    case DataTypeKind::kInteger:
      return DpiArgValue::FromLogicVec(
          SvLogicVecVal{static_cast<uint32_t>(NumericToInt(v)), 0});
    case DataTypeKind::kByte: {
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int8_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
    case DataTypeKind::kShortint: {
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int16_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
    case DataTypeKind::kString:
      return v.type == DataTypeKind::kString ? v : DpiArgValue::FromString("");
    case DataTypeKind::kChandle:
      return v.type == DataTypeKind::kChandle
                 ? v
                 : DpiArgValue::FromChandle(nullptr);
    default: {
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int32_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
  }
}

void DpiRuntime::RegisterImport(DpiRtFunction func) {
  import_global_index_.emplace(DpiGlobalName(func), imports_.size());
  import_index_[func.sv_name] = imports_.size();
  imports_.push_back(std::move(func));
}

const DpiRtFunction* DpiRuntime::FindImport(std::string_view sv_name) const {
  auto it = import_index_.find(sv_name);
  if (it == import_index_.end()) return nullptr;
  return &imports_[it->second];
}

const DpiRtFunction* DpiRuntime::FindImportIn(std::string_view unit_scope,
                                              std::string_view sv_name) const {
  if (!unit_scope.empty()) {
    const DpiRtFunction* own =
        FindImport(std::string(unit_scope) + "::" + std::string(sv_name));
    if (own != nullptr) return own;
  }
  return FindImport(sv_name);
}

bool DpiRuntime::HasImport(std::string_view sv_name) const {
  return import_index_.count(sv_name) != 0;
}

uint32_t DpiRuntime::ImportCount() const {
  return static_cast<uint32_t>(imports_.size());
}

namespace {
std::string ExportInstanceKey(std::string_view sv_name,
                              std::string_view scope_name) {
  std::string key(scope_name);
  key += '\0';
  key += sv_name;
  return key;
}
}  // namespace

void DpiRuntime::RegisterExport(DpiRtExport exp) {
  exp.is_context = true;
  if (!exp.scope_name.empty()) {
    export_scope_index_[ExportInstanceKey(exp.sv_name, exp.scope_name)] =
        exports_.size();
  }
  export_global_index_.emplace(DpiGlobalName(exp), exports_.size());
  export_index_[exp.sv_name] = exports_.size();
  exports_.push_back(std::move(exp));
}

const DpiRtExport* DpiRuntime::FindExport(std::string_view sv_name) const {
  auto it = export_index_.find(sv_name);
  if (it == export_index_.end()) return nullptr;
  return &exports_[it->second];
}

const DpiRtExport* DpiRuntime::FindExportInScope(
    std::string_view sv_name, std::string_view scope_name) const {
  auto it = export_scope_index_.find(ExportInstanceKey(sv_name, scope_name));
  if (it == export_scope_index_.end()) return nullptr;
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

namespace {

void AppendArgKey(std::string& key, const DpiArgValue& arg) {
  key += std::to_string(static_cast<int>(arg.type));
  key += ':';
  if (arg.IsArray()) {
    key += '[';
    for (const DpiArgValue& element : arg.elements) {
      AppendArgKey(key, element);
      key += ',';
    }
    key += ']';
    return;
  }
  if (arg.IsWideVec()) {
    for (const SvLogicVecVal& word : arg.AsLogicVecWords()) {
      key += std::to_string(word.aval) + '/' + std::to_string(word.bval) + ',';
    }
    return;
  }
  switch (arg.type) {
    case DataTypeKind::kString:
      key += arg.AsString();
      break;
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
      key += std::to_string(arg.AsReal());
      break;
    case DataTypeKind::kChandle:
      key += std::to_string(reinterpret_cast<uintptr_t>(arg.AsChandle()));
      break;
    case DataTypeKind::kBit:
      key += std::to_string(static_cast<int>(arg.AsBit()));
      break;
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      key += std::to_string(static_cast<int>(arg.AsLogic()));
      break;
    case DataTypeKind::kInteger:
      key += std::to_string(arg.AsLogicVec().aval);
      key += '/';
      key += std::to_string(arg.AsLogicVec().bval);
      break;
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      key += std::to_string(arg.AsLongint());
      break;
    default:
      key += std::to_string(arg.AsInt());
      break;
  }
}

std::string PureCallArgKey(std::string_view sv_name,
                           const std::vector<DpiArgValue>& args) {
  std::string key(sv_name);
  for (const auto& arg : args) {
    key += '|';
    AppendArgKey(key, arg);
  }
  return key;
}

}  // namespace

bool DpiRuntime::ImportCallIsRemovable(std::string_view sv_name) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr) return false;
  return func->is_pure;
}

DpiArgValue DpiRuntime::CallImportReusingPureResult(
    std::string_view sv_name, const std::vector<DpiArgValue>& args) {
  const auto* func = FindImport(sv_name);
  if (func == nullptr || !func->is_pure) return CallImport(sv_name, args);

  std::string key = PureCallArgKey(sv_name, args);
  auto it = pure_results_.find(key);
  if (it != pure_results_.end()) return it->second;

  DpiArgValue result = CallImport(sv_name, args);
  pure_results_.emplace(std::move(key), result);
  return result;
}

DpiArgValue DpiRuntime::UndeterminedOutputValue(DataTypeKind type,
                                                uint32_t width) {
  if (width > DpiInlineValueBits(type)) {
    return DpiArgValue::FromLogicVecWords(
        std::vector<SvLogicVecVal>(DpiCanonicalWordCount(width),
                                   SvLogicVecVal{0, 0}),
        width, type);
  }
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
    case DataTypeKind::kInteger:
      return DpiArgValue::FromLogicVec(SvLogicVecVal{});
    default:
      return DpiArgValue::FromInt(0);
  }
}

DpiArgValue DpiRuntime::CallImportWithArgs(
    std::string_view sv_name, std::vector<DpiArgValue>& actuals) const {
  const auto* func = FindImport(sv_name);
  if (!func) return DpiArgValue::FromInt(0);

  std::vector<DpiArgValue> callee = actuals;
  for (size_t i = 0; i < func->args.size() && i < callee.size(); ++i) {
    if (func->args[i].direction == Direction::kOutput) {
      DpiArgValue seeded =
          UndeterminedOutputValue(func->args[i].type, func->args[i].width);
      seeded.ranges = callee[i].ranges;
      callee[i] = std::move(seeded);
    } else {
      callee[i] = CoerceArgValue(callee[i], func->args[i].type);
    }
  }

  DpiArgValue result = DpiArgValue::FromInt(0);
  if (func->arg_impl) {
    result = func->arg_impl(callee);
  } else if (func->impl) {
    result = func->impl(callee);
  }

  if (DpiCurrentDisabledState()) {
    return UndeterminedOutputValue(func->return_type);
  }

  for (size_t i = 0; i < func->args.size() && i < actuals.size(); ++i) {
    Direction dir = func->args[i].direction;
    if (dir == Direction::kOutput || dir == Direction::kInout) {
      actuals[i] = CoerceArgValue(callee[i], actuals[i].type);
    }
  }
  return result;
}

DpiArgValue DpiRuntime::CallImportDetectingChanges(
    std::string_view sv_name, std::vector<DpiArgValue>& actuals,
    std::vector<DpiArgValueChange>& changes) const {
  const auto* func = FindImport(sv_name);
  if (!func) return DpiArgValue::FromInt(0);

  std::vector<DpiArgValue> before = actuals;

  DpiArgValue result = CallImportWithArgs(sv_name, actuals);

  for (size_t i = 0; i < func->args.size() && i < actuals.size(); ++i) {
    Direction dir = func->args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    if (SameArgValue(before[i], actuals[i])) continue;
    changes.push_back(DpiArgValueChange{i, before[i], actuals[i]});
  }
  return result;
}

void DpiRuntime::EnterContextImportCall(std::string_view sv_name,
                                        DpiScope decl_scope, bool is_task) {
  if (call_chain_.empty()) DpiSetCurrentDisabledState(false);
  PushScope(std::move(decl_scope));
  call_chain_.push_back({sv_name, true, is_task});
}

void DpiRuntime::EnterNoncontextImportCall(std::string_view sv_name,
                                           bool is_task) {
  if (call_chain_.empty()) DpiSetCurrentDisabledState(false);
  bool from_stack =
      !scope_stack_.empty() && current_scope_ == scope_stack_.back();
  call_chain_.push_back({sv_name, false, is_task, current_scope_, from_stack});
}

void DpiRuntime::EnterDeclaredImportCall(std::string_view sv_name,
                                         DpiScope decl_scope) {
  const auto* func = FindImport(sv_name);
  const bool kIsTask = func != nullptr && func->is_task;
  if (func == nullptr || func->is_pure || !func->is_context) {
    EnterNoncontextImportCall(sv_name, kIsTask);
    return;
  }
  EnterContextImportCall(sv_name, std::move(decl_scope), kIsTask);
}

void DpiRuntime::LeaveImportCall() {
  if (call_chain_.empty()) return;
  if (!call_chain_.back().is_task) {
    VerifyImportFunctionReturnUnderDisable(call_chain_.back().sv_name);
  }
  bool had_context = call_chain_.back().is_context;
  const DpiScope* entry_scope = call_chain_.back().entry_scope;
  bool entry_scope_from_stack = call_chain_.back().entry_scope_from_stack;
  call_chain_.pop_back();
  if (call_chain_.empty()) DpiSetCurrentDisabledState(false);
  if (had_context) {
    PopScope();
    return;
  }
  if (entry_scope_from_stack) {
    current_scope_ = scope_stack_.empty() ? nullptr : scope_stack_.back();
    return;
  }
  current_scope_ = entry_scope;
}

uint32_t DpiRuntime::ImportCallDepth() const {
  return static_cast<uint32_t>(call_chain_.size());
}

bool DpiRuntime::ChainRootIsContext() const {
  if (call_chain_.empty()) return false;
  return call_chain_.front().is_context;
}

bool DpiRuntime::InCallChain() const {
  const size_t kStart = chain_starts_.empty() ? 0 : chain_starts_.back();
  return call_chain_.size() > kStart;
}

uint32_t DpiRuntime::OpenCallChainCount() const {
  if (call_chain_.empty()) return 0;
  uint32_t open = 1;
  for (size_t start : chain_starts_) {
    if (call_chain_.size() > start) ++open;
  }
  return open;
}

bool DpiRuntime::InContextCallChain() const {
  return InCallChain() && call_chain_.back().is_context;
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
      DpiSetCurrentDisabledState(true);
      return 1;
    case DpiDisableTarget::kExportItself:
    case DpiDisableTarget::kNone:
    default:
      DpiSetCurrentDisabledState(false);
      return 0;
  }
}

void* DpiRuntime::PackedArgRef(std::string_view sv_name,
                               void* actual_data) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr ||
      func->packed_arg_passing != DpiPackedArgPassing::kSv31aReference) {
    return nullptr;
  }
  return actual_data;
}

bool DpiRuntime::IsDisabledState() const { return DpiCurrentDisabledState(); }

bool DpiRuntime::CheckImportedSubroutineDisableReturn(
    bool is_task, int task_return_value) const {
  if (!DpiCurrentDisabledState()) return true;
  if (is_task) {
    return task_return_value == 1;
  }
  return DpiCurrentDisableAcknowledged();
}

bool DpiRuntime::VerifyImportTaskReturnUnderDisable(std::string_view sv_name,
                                                    int task_return_value) {
  if (CheckImportedSubroutineDisableReturn(true, task_return_value)) {
    return true;
  }
  IssueDisableProtocolFatalError(
      "35.9 item b): imported task '" + std::string(sv_name) + "' returned " +
      std::to_string(task_return_value) +
      " while a disable was in effect; under a disable, 1 is the only value an "
      "imported task may give back");
  return false;
}

bool DpiRuntime::VerifyImportFunctionReturnUnderDisable(
    std::string_view sv_name) {
  if (CheckImportedSubroutineDisableReturn(false, 0)) {
    return true;
  }
  IssueDisableProtocolFatalError(
      "35.9 item c): imported function '" + std::string(sv_name) +
      "' returned while a disable was in effect without having called "
      "svAckDisabledState()");
  return false;
}

bool DpiRuntime::VerifyImportReturnUnderDisable(int task_return_value) {
  if (call_chain_.empty()) return true;
  std::string_view sv_name = call_chain_.back().sv_name;
  if (call_chain_.back().is_task) {
    return VerifyImportTaskReturnUnderDisable(sv_name, task_return_value);
  }
  return VerifyImportFunctionReturnUnderDisable(sv_name);
}

void DpiRuntime::IssueDisableProtocolFatalError(const std::string& message) {
  if (disable_protocol_fatal_) return;
  disable_protocol_fatal_ = true;
  disable_protocol_fatal_message_ = message;
  std::cerr << "FATAL: " << message << "\n";
}

bool DpiRuntime::DisableProtocolFatalErrorIssued() const {
  return disable_protocol_fatal_;
}

const std::string& DpiRuntime::DisableProtocolFatalError() const {
  return disable_protocol_fatal_message_;
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

}  // namespace delta
