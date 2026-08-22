#include <string>
#include <string_view>
#include <vector>

#include "simulator/dpi_runtime.h"

namespace delta {

DpiExportCallStatus DpiRuntime::CheckExportCallPermitted(
    const DpiRtExport* exp, std::string_view sv_name) {
  // §35.9 item d): once an imported subroutine has entered the disabled state,
  // it is illegal for the current call to make any further calls to exported
  // subroutines. This applies whatever the chain's context property or the kind
  // of export, so it is checked ahead of the §35.8 and §35.5.3 rules.
  if (DpiCurrentDisabledState()) {
    // §35.9: the simulator checks item d) and issues a fatal simulation error
    // where it is not followed. The export is not entered either way, so no
    // work the disabled subroutine asked for is done.
    std::string caller(call_chain_.empty() ? std::string_view()
                                           : call_chain_.back().sv_name);
    IssueDisableProtocolFatalError("35.9 item d): imported subroutine '" +
                                   caller + "' called exported subroutine '" +
                                   std::string(sv_name) +
                                   "' after entering the disabled state");
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
  return DpiExportCallStatus::kOk;
}

DpiExportCallStatus DpiRuntime::CallExportFromImport(
    std::string_view sv_name, const std::vector<DpiArgValue>& args,
    DpiArgValue* out_result) {
  // §35.5.3: the instance of the export this call reaches is the one the
  // chain's current scope declares -- the import declaration's instantiated
  // scope until svSetScope names another. Where the current scope declares no
  // instance of this name, the lookup falls back to the name alone, which is
  // what an export registered without a scope is reachable under.
  const auto* exp = current_scope_ != nullptr
                        ? FindExportInScope(sv_name, current_scope_->name)
                        : nullptr;
  if (exp == nullptr) exp = FindExport(sv_name);
  DpiExportCallStatus barred = CheckExportCallPermitted(exp, sv_name);
  if (barred != DpiExportCallStatus::kOk) return barred;
  // §35.5.3: when the export call returns, the chain context shall be the
  // value it had at the point the export was invoked. Snapshot and restore
  // around the call so that any scope changes performed by the export (or
  // by code it called) do not leak back to the import chain.
  const DpiScope* saved_scope = current_scope_;
  // The instance selected above is entered directly rather than through
  // CallExport, which looks the export up by name and so would enter whichever
  // instance holds the name index rather than the one this scope declares.
  DpiArgValue result =
      (exp != nullptr && exp->impl) ? exp->impl(args) : DpiArgValue::FromInt(0);
  current_scope_ = saved_scope;
  if (exp != nullptr && exp->is_task) {
    // §35.8: "SystemVerilog tasks do not have return value types. The return
    // value of an exported task is an int value that indicates if a disable is
    // active or not on the current execution thread." The foreign caller gets
    // that indication, not what the body handed back, which stands for no
    // result the clause gives a task. ReturnFromExportUnderDisable sets the
    // thread state read here.
    result = DpiArgValue::FromInt(DpiCurrentDisabledState() ? 1 : 0);
  }
  if (out_result) *out_result = result;
  return DpiExportCallStatus::kOk;
}

}  // namespace delta
