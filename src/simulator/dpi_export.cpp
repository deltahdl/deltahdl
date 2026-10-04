#include "simulator/dpi_export.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_formal_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/dpi_task_call.h"
#include "simulator/eval_function_internal.h"
#include "simulator/sim_context.h"

namespace delta {

std::string DpiInstanceScopeName(std::string_view prefix,
                                 const SimContext& ctx) {
  std::string_view path = prefix;
  if (!path.empty() && path.back() == '.') path.remove_suffix(1);
  const std::string_view kTop = ctx.FirstTopModule();
  if (path.empty()) return std::string(kTop);
  if (kTop.empty() || ctx.IsParallelTop(path.substr(0, path.find('.')))) {
    return std::string(path);
  }
  return std::string(kTop) + "." + std::string(path);
}

void RegisterModuleDpiExports(const RtlirModule* mod, std::string_view prefix,
                              SimContext& ctx) {
  const ScopeMap kScope = DpiParameterScope(*mod);
  for (const ModuleItem* item : mod->dpi_export_decls) {
    const std::string kKey = std::string(prefix) + std::string(item->name);
    const ModuleItem* subroutine = ctx.FindFunction(kKey);
    DpiRuntime& dpi = ctx.AcquireDpiRuntime();
    DpiRtExport exp;
    exp.sv_name = item->name;
    // §35.4: "If a global name is not explicitly given, it shall be the same
    // as the SystemVerilog subroutine name."
    exp.c_name = item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
    exp.scope_name = DpiInstanceScopeName(prefix, ctx);
    exp.is_task = item->dpi_is_task;
    // §H.9.3: svGetScopeFromName finds the instance by this name.
    DpiRegisterScope(exp.scope_name);
    if (subroutine != nullptr) {
      exp.return_type =
          exp.is_task ? DataTypeKind::kVoid : subroutine->return_type.kind;
      for (const FunctionArg& arg : subroutine->func_args) {
        exp.args.push_back(DpiFormalOfArg(arg, kScope));
      }
    }
    if (subroutine != nullptr) {
      // The formals are read at the call, ResolveDpiFormalTypes having
      // resolved them in place once the design is lowered, so the export is
      // named by its position rather than copied.
      const size_t kIndex = dpi.Exports().size();
      std::string_view key = *ctx.GetArena().Create<std::string>(kKey);
      DpiRuntime* runtime = &dpi;
      SimContext* run = &ctx;
      if (exp.is_task) {
        // §35.8: a task may consume time, so the process that enabled the
        // calling import runs it (RunExportedTaskFromC).
        exp.arg_impl = [runtime, kIndex, key](std::vector<DpiArgValue>& args) {
          return RunExportedTaskFromC(runtime->Exports()[kIndex], key, args);
        };
      } else {
        exp.arg_impl = [runtime, run, kIndex,
                        key](std::vector<DpiArgValue>& args) {
          return CallDpiExportedFunction(key, runtime->Exports()[kIndex], args,
                                         *run);
        };
      }
    }
    dpi.RegisterExport(std::move(exp));
  }
}

}  // namespace delta
