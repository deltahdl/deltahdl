#include <cstddef>

#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

SyncHandle SyncActualOf(const FunctionArg& param, const Expr* actual,
                        const ModuleItem* func, SimContext& ctx, Arena& arena) {
  SyncHandle handle;
  handle.kind =
      SyncKindOfType(param.data_type, ctx.SubroutinePackage(func), ctx);
  if (handle.kind == SyncKind::kNone || actual == nullptr) return handle;
  CalleeScopeAside aside(ctx);
  return ResolveSyncActual(handle.kind, actual, ctx, arena);
}

void BindRefSyncFormal(const FunctionArg& param, const Expr* actual,
                       const ModuleItem* func, SimContext& ctx, Arena& arena) {
  SyncHandle sync = SyncActualOf(param, actual, func, ctx, arena);
  if (sync.kind == SyncKind::kNone) return;
  if (Variable* var = ctx.FindLocalVariable(param.name)) {
    BindSyncFormal(sync, var, ctx);
  }
}

bool TryBindEventFormal(const Expr* call, int arg_index,
                        const FunctionArg& param, SimContext& ctx) {
  if (param.direction != Direction::kInput ||
      param.data_type.kind != DataTypeKind::kEvent || arg_index < 0) {
    return false;
  }
  const Expr* actual = call->args[static_cast<size_t>(arg_index)];
  if (actual == nullptr || actual->kind != ExprKind::kIdentifier) return false;
  Variable* event = nullptr;
  {
    CalleeScopeAside aside(ctx);
    event = ctx.FindVariable(actual->text);
  }
  if (event == nullptr || !event->is_event) return false;
  ctx.AliasLocalVariable(param.name, event);
  return true;
}

}  // namespace delta
