#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

namespace delta {

namespace {

std::vector<DpiArgValue> ActualsAsDeclaredTypes(
    const DpiRtExport& exp, const std::vector<DpiArgValue>& args) {
  std::vector<DpiArgValue> coerced = args;
  for (size_t i = 0; i < exp.args.size() && i < coerced.size(); ++i) {
    coerced[i] = CoerceArgValue(coerced[i], exp.args[i].type);
  }
  return coerced;
}

DpiArgValue ResultAsDeclaredType(const DpiRtExport& exp,
                                 const DpiArgValue& result) {
  if (exp.return_type == DataTypeKind::kVoid) return result;
  return CoerceArgValue(result, exp.return_type);
}

DpiArgValue CallExportBody(const DpiRtExport& exp,
                           const std::vector<DpiArgValue>& args,
                           std::vector<DpiArgValue>* written = nullptr) {
  if (exp.arg_impl) {
    std::vector<DpiArgValue> actuals = ActualsAsDeclaredTypes(exp, args);
    DpiArgValue result = ResultAsDeclaredType(exp, exp.arg_impl(actuals));
    if (written != nullptr) *written = std::move(actuals);
    return result;
  }
  if (!exp.impl) return DpiArgValue::FromInt(0);
  return ResultAsDeclaredType(exp, exp.impl(ActualsAsDeclaredTypes(exp, args)));
}

}  // namespace

DpiArgValue DpiRuntime::CallExport(std::string_view sv_name,
                                   const std::vector<DpiArgValue>& args) const {
  const auto* exp = FindExport(sv_name);
  if (!exp || !exp->impl) return DpiArgValue::FromInt(0);
  return CallExportBody(*exp, args);
}

DpiExportCallStatus DpiRuntime::CheckExportCallPermitted(
    const DpiRtExport* exp, std::string_view sv_name) {
  if (DpiCurrentDisabledState()) {
    std::string caller(call_chain_.empty() ? std::string_view()
                                           : call_chain_.back().sv_name);
    IssueDisableProtocolFatalError("35.9 item d): imported subroutine '" +
                                   caller + "' called exported subroutine '" +
                                   std::string(sv_name) +
                                   "' after entering the disabled state");
    return DpiExportCallStatus::kDisabledStateExportCall;
  }
  if (!call_chain_.empty() && !call_chain_.back().is_task && exp != nullptr &&
      exp->is_task) {
    return DpiExportCallStatus::kFunctionCallsTask;
  }
  if (call_chain_.empty() || !call_chain_.back().is_context) {
    return DpiExportCallStatus::kNoncontextChain;
  }
  if (exp != nullptr && !exp->scope_name.empty() && current_scope_ != nullptr &&
      exp->scope_name != current_scope_->name) {
    return DpiExportCallStatus::kScopeMismatch;
  }
  return DpiExportCallStatus::kOk;
}

DpiExportCallStatus DpiRuntime::CallExportFromImport(
    std::string_view sv_name, const std::vector<DpiArgValue>& args,
    DpiArgValue* out_result, std::vector<DpiArgValue>* written) {
  const auto* exp = current_scope_ != nullptr
                        ? FindExportInScope(sv_name, current_scope_->name)
                        : nullptr;
  if (exp == nullptr) exp = FindExport(sv_name);
  DpiExportCallStatus barred = CheckExportCallPermitted(exp, sv_name);
  if (barred != DpiExportCallStatus::kOk) return barred;
  const DpiScope* saved_scope = current_scope_;
  chain_starts_.push_back(call_chain_.size());
  DpiArgValue result = exp != nullptr ? CallExportBody(*exp, args, written)
                                      : DpiArgValue::FromInt(0);
  chain_starts_.pop_back();
  current_scope_ = saved_scope;
  if (exp != nullptr && exp->is_task) {
    result = DpiArgValue::FromInt(DpiCurrentDisabledState() ? 1 : 0);
  }
  if (out_result) *out_result = result;
  return DpiExportCallStatus::kOk;
}

}  // namespace delta
