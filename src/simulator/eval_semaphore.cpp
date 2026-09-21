#include "simulator/eval_semaphore.h"

#include <cstdint>
#include <string>
#include <string_view>

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

// §26.3 admits a package-qualified semaphore as the receiver, `p::sem.get()`,
// found under the "p.sem" key ExtractHandleMethodCallParts answers, given the
// context's arena as the key's lifetime since the signature carries none.
// This is asked of every call statement, so the method's name is matched
// before the key is made. §8.7 with §15.3.1 (printed page 373 of IEEE
// 1800-2023): a semaphore declared as a class property is each object's
// own, so a bare `s` inside a method of the class, `this.s` and a handle's
// `c.s` name the object's (ResolveSyncProperty) ahead of the run's tables,
// which hold no object's; resolved by name alone, `s.get(1)` in a method
// reached no bucket.
SemaphoreObject* SemaphoreCallTarget(const Expr* expr, SimContext& ctx,
                                     std::string_view method) {
  if (!expr || expr->kind != ExprKind::kCall) return nullptr;
  const auto* access = expr->lhs;
  if (!access || access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->rhs || access->rhs->text != method) return nullptr;
  SyncProperty prop = ResolveSyncProperty(access->lhs, ctx, ctx.GetArena());
  if (prop.kind != SyncKind::kNone) {
    return SemaphoreOfProperty(prop, method, access->rhs->range.start, ctx);
  }
  // §13.5.1 (printed 348) with §8.2 (printed 180): a `semaphore s` formal is
  // a handle to the actual's bucket (BindSyncFormal), asked next.
  if (SemaphoreObject* sem = SemaphoreOfFormal(access->lhs, ctx)) return sem;
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, ctx.GetArena(), parts))
    return nullptr;
  return ctx.FindSemaphore(parts.var_name);
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

// The receiver of a call as a report spells it: a bare `s`, a method's
// `this.s`, a handle's `c.s` or a package's `p::s`, each as written.
static std::string ReceiverSpelling(const Expr* recv) {
  if (recv->kind != ExprKind::kMemberAccess) return std::string(recv->text);
  return ReceiverSpelling(recv->lhs) +
         (recv->is_scope_resolution ? "::" : ".") +
         std::string(recv->rhs->text);
}

// §15.3.3 (printed page 373 of IEEE 1800-2023) inside a function body:
// get() takes the keys where the bucket holds enough, as SemaphoreGetAwaiter
// does before it would park the process, and a bucket with too few, on which it
// would wait, is §13.4's report (printed 340) with the bucket as it was. The
// receiver resolves through SemaphoreCallTarget, so a method's bare `s.get(1)`
// on a class property reaches the object's bucket as a module's reaches the
// module's. Served by the expression evaluator, which answers put() and
// try_get() alone, a function's `s.get(1)` left the bucket full.
bool TryExecSemaphoreCallInFunction(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  auto* sem = SemaphoreCallTarget(expr, ctx, "get");
  if (!sem) return false;
  if (sem->Get(SemaphoreKeyArg(expr, ctx, arena, 1)) != SemGetStatus::kBlock)
    return true;
  ctx.GetDiag().Error(expr->range.start,
                      "semaphore get(): '" + ReceiverSpelling(expr->lhs->lhs) +
                          "' has too few keys, so the call would block "
                          "inside a function",
                      Subclause("13.4"));
  return true;
}

// The scoped target is the scope resolution of two identifiers the parser
// leaves `p::name` as, its key built as ExtractHandleAccessParts builds a
// scoped receiver's, and FindSemaphore and FindMailbox answer the dotted key
// as they answer a bare name. Taken as an identifier alone, `p1::t = new(1)`
// on a package's `semaphore t` was declined here and by every later arm, so
// the statement fell to the generic store and the bucket stayed empty.
std::string_view ScopedOrBareTargetKey(const Expr* lhs, Arena& arena) {
  if (lhs == nullptr) return {};
  // §3.12.1 (printed page 56): a `$unit::arr` identifier is the unit's
  // object under "$unit.arr" (DeclaredKindsKey), so `$unit::arr[0]`
  // (TryArrayElementSelect in eval_select.cpp) reads the unit's element past
  // a module's own arr, which the text alone named; any other identifier is
  // its text, as before.
  if (lhs->kind == ExprKind::kIdentifier) {
    if (lhs->scope_prefix != "$unit") return lhs->text;
    return *arena.Create<std::string>(DeclaredKindsKey(lhs));
  }
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      lhs->lhs == nullptr || lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return *arena.Create<std::string>(std::string(lhs->lhs->text) + "." +
                                    std::string(lhs->rhs->text));
}

// §8.7 with §15.3.1: the target may be a class property, `s = new(2)` in a
// method or `c.s = new(2)` through a handle, whose bucket is the object's
// alone (BuildSyncProperty). §15.3.1 (printed page 373 of IEEE 1800-2023)
// has new() return the semaphore handle, so the variable the statement assigns
// refers to the bucket from here on and §8.4 (printed 182) compares it
// unequal to null (HoldSyncVariable); the bucket alone was filled, and a
// `semaphore s;` read as null after its `s = new(2)`.
bool TrySemaphoreNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  SyncProperty prop = ResolveSyncProperty(stmt->lhs, ctx, arena);
  if (prop.kind == SyncKind::kSemaphore) {
    BuildSyncProperty(prop, stmt->rhs, ctx, arena);
    return true;
  }
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return false;
  auto* sem = ctx.FindSemaphore(key);
  if (!sem) return false;
  // §15.3.1: new() takes the key count as its one argument and defaults it to
  // zero, so a bucket built without one starts empty.
  sem->key_count = SemaphoreKeyArg(stmt->rhs, ctx, arena, 0);
  HoldSyncVariable(key, ctx);
  return true;
}

}  // namespace delta
