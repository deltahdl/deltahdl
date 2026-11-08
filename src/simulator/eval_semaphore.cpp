#include "simulator/eval_semaphore.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"
#include "simulator/sync_variable.h"

namespace delta {

static const Expr* MethodAccessOf(const Expr* expr) {
  if (expr == nullptr) return nullptr;
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution) {
    return nullptr;
  }
  return access;
}

static std::string_view CalledMethodName(const Expr* expr) {
  if (const Expr* access = MethodAccessOf(expr)) return access->rhs->text;
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr) {
    return expr->lhs->text;
  }
  return {};
}

SemaphoreObject* SemaphoreCallTarget(const Expr* expr, SimContext& ctx,
                                     std::string_view method) {
  const Expr* access = MethodAccessOf(expr);
  if (!access) return BuiltinBaseSemaphore(expr, method, ctx, ctx.GetArena());
  if (!access->rhs || access->rhs->text != method) return nullptr;
  SyncProperty prop = ResolveSyncProperty(access->lhs, ctx, ctx.GetArena());
  if (prop.kind != SyncKind::kNone) {
    return SemaphoreOfProperty(prop, method, access->rhs->range.start, ctx);
  }
  if (SemaphoreObject* sem = SemaphoreOfFormal(access->lhs, ctx)) return sem;
  if (SemaphoreObject* sem =
          ContainedSemaphoreOf(access->lhs, ctx, ctx.GetArena())) {
    return sem;
  }
  if (SemaphoreObject* base =
          BuiltinBaseSemaphore(expr, method, ctx, ctx.GetArena())) {
    return base;
  }
  MethodCallParts parts;
  if (ExtractHandleAccessParts(access, ctx.GetArena(), parts)) {
    return ctx.FindSemaphore(parts.var_name);
  }
  std::string_view key = ScopedOrBareTargetKey(access->lhs, ctx.GetArena());
  return key.empty() ? nullptr : ctx.FindSemaphore(key);
}

int32_t SemaphoreKeyArg(const Expr* expr, SimContext& ctx, Arena& arena,
                        int32_t absent) {
  if (expr->args.empty() || !expr->args[0]) return absent;
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return static_cast<int32_t>(static_cast<uint32_t>(val.ToUint64()));
}

bool ReportNegativeKeyCount(const Expr* expr, int32_t count,
                            std::string_view subclause, SimContext& ctx) {
  if (count >= 0) return false;
  ctx.GetDiag().Error(expr->range.start,
                      "semaphore " + std::string(CalledMethodName(expr)) +
                          "(): the key count " + std::to_string(count) +
                          " is negative",
                      Subclause(subclause));
  return true;
}

bool TryEvalSemaphoreMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (auto* sem = SemaphoreCallTarget(expr, ctx, "put")) {
    int32_t count = SemaphoreKeyArg(expr, ctx, arena, 1);
    if (!ReportNegativeKeyCount(expr, count, "15.3.2", ctx)) sem->Put(count);
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (auto* sem = SemaphoreCallTarget(expr, ctx, "try_get")) {
    int32_t count = SemaphoreKeyArg(expr, ctx, arena, 1);
    int32_t got = ReportNegativeKeyCount(expr, count, "15.3.4", ctx)
                      ? 0
                      : sem->TryGet(count);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(got));
    return true;
  }
  return false;
}

static std::string ReceiverSpelling(const Expr* recv) {
  if (recv->kind != ExprKind::kMemberAccess) return std::string(recv->text);
  return ReceiverSpelling(recv->lhs) +
         (recv->is_scope_resolution ? "::" : ".") +
         std::string(recv->rhs->text);
}

static std::string ReceiverOfCall(const Expr* expr) {
  const Expr* access = MethodAccessOf(expr);
  return access != nullptr ? ReceiverSpelling(access->lhs) : "this";
}

bool TryExecSemaphoreCallInFunction(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  auto* sem = SemaphoreCallTarget(expr, ctx, "get");
  if (!sem) return false;
  int32_t count = SemaphoreKeyArg(expr, ctx, arena, 1);
  if (ReportNegativeKeyCount(expr, count, "15.3.3", ctx)) return true;
  if (sem->Get(count) != SemGetStatus::kBlock) return true;
  ctx.GetDiag().Error(expr->range.start,
                      "semaphore get(): '" + ReceiverOfCall(expr) +
                          "' has too few keys, so the call would block "
                          "inside a function",
                      Subclause("13.4"));
  return true;
}

std::string_view ScopedOrBareTargetKey(const Expr* lhs, Arena& arena) {
  if (lhs == nullptr) return {};
  if (lhs->kind == ExprKind::kIdentifier) {
    if (lhs->scope_prefix != "$unit") return lhs->text;
    return *arena.Create<std::string>(DeclaredKindsKey(lhs));
  }
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  if (!lhs->is_scope_resolution) {
    std::string path = HierarchicalReferenceName(lhs);
    if (path.empty()) return {};
    return *arena.Create<std::string>(std::move(path));
  }
  if (lhs->lhs->kind != ExprKind::kIdentifier) return {};
  return *arena.Create<std::string>(std::string(lhs->lhs->text) + "." +
                                    std::string(lhs->rhs->text));
}

bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  SyncProperty prop = ResolveSyncProperty(stmt->lhs, ctx, arena);
  if (prop.kind == SyncKind::kSemaphore) {
    BuildSyncProperty(prop, stmt->rhs, ctx, arena);
    return true;
  }
  if (TryLocalSyncNewAssign(stmt, ctx, arena)) return true;
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return false;
  SemaphoreObject** slot = ctx.SemaphoreSlot(key);
  if (slot == nullptr) return false;
  int32_t keys = SemaphoreKeyArg(stmt->rhs, ctx, arena, 0);
  if (*slot == nullptr || (*slot)->shared) {
    *slot = ctx.GetArena().Create<SemaphoreObject>(keys);
  } else {
    (*slot)->key_count = keys;
  }
  HoldSyncVariable(key, ctx);
  return true;
}

}  // namespace delta
