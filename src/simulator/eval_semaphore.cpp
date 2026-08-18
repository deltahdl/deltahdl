#include "simulator/eval_semaphore.h"

#include <cstdint>
#include <string_view>

#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

namespace delta {

SemaphoreObject* SemaphoreCallTarget(const Expr* expr, SimContext& ctx,
                                     std::string_view method) {
  if (!expr || expr->kind != ExprKind::kCall) return nullptr;
  const auto* access = expr->lhs;
  if (!access || access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (access->rhs->text != method) return nullptr;
  return ctx.FindSemaphore(access->lhs->text);
}

int32_t SemaphoreKeyArg(const Expr* expr, SimContext& ctx, Arena& arena,
                        int32_t absent) {
  if (expr->args.empty() || !expr->args[0]) return absent;
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return static_cast<int32_t>(static_cast<uint32_t>(val.ToUint64()));
}

bool TryEvalSemaphoreMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (auto* sem = SemaphoreCallTarget(expr, ctx, "put")) {
    sem->Put(SemaphoreKeyArg(expr, ctx, arena, 1));
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (auto* sem = SemaphoreCallTarget(expr, ctx, "try_get")) {
    auto got = sem->TryGet(SemaphoreKeyArg(expr, ctx, arena, 1));
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(got));
    return true;
  }
  return false;
}

bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  auto* sem = ctx.FindSemaphore(stmt->lhs->text);
  if (!sem) return false;
  // §15.3.1: new() takes the key count as its one argument and defaults it to
  // zero, so a bucket built without one starts empty.
  sem->key_count = SemaphoreKeyArg(stmt->rhs, ctx, arena, 0);
  return true;
}

}  // namespace delta
