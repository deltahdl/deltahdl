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

// §13.3 and §13.4 make the argument list of a call with no arguments
// optional, so `s.put;` and `r = s.try_get` are the calls `s.put()` and
// `s.try_get()`: the member access of either form, or null for neither.
static const Expr* MethodAccessOf(const Expr* expr) {
  if (expr == nullptr) return nullptr;
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution) {
    return nullptr;
  }
  return access;
}

// The name of the method the call `expr` makes, through a receiver or, inside
// a class extending the semaphore, unqualified.
static std::string_view CalledMethodName(const Expr* expr) {
  if (const Expr* access = MethodAccessOf(expr)) return access->rhs->text;
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr) {
    return expr->lhs->text;
  }
  return {};
}

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
  const Expr* access = MethodAccessOf(expr);
  if (!access) return BuiltinBaseSemaphore(expr, method, ctx, ctx.GetArena());
  if (!access->rhs || access->rhs->text != method) return nullptr;
  SyncProperty prop = ResolveSyncProperty(access->lhs, ctx, ctx.GetArena());
  if (prop.kind != SyncKind::kNone) {
    return SemaphoreOfProperty(prop, method, access->rhs->range.start, ctx);
  }
  // §13.5.1 (printed 348) with §8.2 (printed 180): a `semaphore s` formal is
  // a handle to the actual's bucket (BindSyncFormal), asked next.
  if (SemaphoreObject* sem = SemaphoreOfFormal(access->lhs, ctx)) return sem;
  // §7.10 and §7.8: an element of a queue or an associative array of
  // semaphores, `q[0].try_get()` (ContainedSemaphoreOf).
  if (SemaphoreObject* sem =
          ContainedSemaphoreOf(access->lhs, ctx, ctx.GetArena())) {
    return sem;
  }
  // §15.2 with §8.13: the base bucket of an object of a class extending the
  // semaphore, reached through a handle, `cs.try_get()`.
  if (SemaphoreObject* base =
          BuiltinBaseSemaphore(expr, method, ctx, ctx.GetArena())) {
    return base;
  }
  MethodCallParts parts;
  if (ExtractHandleAccessParts(access, ctx.GetArena(), parts)) {
    return ctx.FindSemaphore(parts.var_name);
  }
  // §25.3: an interface instance's semaphore reached by its hierarchical name,
  // `c.s.put()` (ScopedOrBareTargetKey).
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

// §15.3.2 and §15.3.4: a negative key count is an error of put() and of
// try_get(), which then returns 0; put() leaves the bucket as it was.
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
// The receiver of the call `expr` as a report spells it, `this` for a call
// written unqualified inside a class extending the semaphore.
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
  if (lhs->kind != ExprKind::kMemberAccess || lhs->lhs == nullptr ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  // §23.6 with §25.3 and §27.4: a hierarchical name, `c.s` for an interface
  // instance's semaphore and `g[1].s` for a generate block instance's, is the
  // key the run holds it under, the instance's prefix and the name joined by
  // dots (CreateChildModuleVariables in lowerer_child.cpp) or the path a
  // generate block member is aliased under (RegisterGenBlockMembers).
  if (!lhs->is_scope_resolution) {
    std::string path = HierarchicalReferenceName(lhs);
    if (path.empty()) return {};
    return *arena.Create<std::string>(std::move(path));
  }
  if (lhs->lhs->kind != ExprKind::kIdentifier) return {};
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
  if (TryLocalSyncNewAssign(stmt, ctx, arena)) return true;
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return false;
  SemaphoreObject** slot = ctx.SemaphoreSlot(key);
  if (slot == nullptr) return false;
  // §15.3.1: new() takes the key count as its one argument and defaults it to
  // zero, so a bucket built without one starts empty.
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
