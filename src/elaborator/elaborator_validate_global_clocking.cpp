// The checks a design's global clocking is held to: §14.13 allows one global
// clocking declaration per scope, §14.14 says where $global_clock may be
// referenced, and §16.9.4 says which sampled value functions require a global
// clocking and where the future ones may appear. They sit beside the rest of
// the clocking checks in elaborator_validate_clocking.cpp and were split out
// of it to keep both files inside the 1000-line limit
// assert-no-oversized-source-files enforces.

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateDuplicateGlobalClocking(const ModuleDecl* decl) {
  const ModuleItem* first_global = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      if (first_global) {
        diag_.Error(item->loc,
                    "only one global clocking block is allowed per scope",
                    Clause::Unread());
        return;
      }
      first_global = item;
    }
  }
}

namespace {

bool ExprRefsGlobalClock(const Expr* e);

// Recurse into every scalar (single-child) sub-expression slot of `e`.
bool AnyScalarChildRefsGlobalClock(const Expr* e) {
  return ExprRefsGlobalClock(e->lhs) || ExprRefsGlobalClock(e->rhs) ||
         ExprRefsGlobalClock(e->condition) ||
         ExprRefsGlobalClock(e->true_expr) ||
         ExprRefsGlobalClock(e->false_expr) || ExprRefsGlobalClock(e->base) ||
         ExprRefsGlobalClock(e->index) || ExprRefsGlobalClock(e->index_end) ||
         ExprRefsGlobalClock(e->repeat_count) ||
         ExprRefsGlobalClock(e->with_expr);
}

bool ExprRefsGlobalClock(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$global_clock") {
    return true;
  }
  if (AnyScalarChildRefsGlobalClock(e)) return true;
  for (auto* a : e->args) {
    if (ExprRefsGlobalClock(a)) return true;
  }
  for (auto* el : e->elements) {
    if (ExprRefsGlobalClock(el)) return true;
  }
  return false;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s);

// Recurse into every nested-statement slot of `s`; returns the first
// descendant hit, or nullptr.
const Expr* FindGlobalClockRefInSubStmts(const Stmt* s) {
  for (auto* sub : s->stmts) {
    if (auto* hit = FindGlobalClockRefInStmt(sub)) return hit;
  }
  if (auto* hit = FindGlobalClockRefInStmt(s->then_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->else_branch)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->body)) return hit;
  if (auto* hit = FindGlobalClockRefInStmt(s->for_body)) return hit;
  for (auto& ci : s->case_items) {
    if (auto* hit = FindGlobalClockRefInStmt(ci.body)) return hit;
  }
  return nullptr;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s) {
  if (!s) return nullptr;
  if (ExprRefsGlobalClock(s->expr)) return s->expr;
  if (ExprRefsGlobalClock(s->lhs)) return s->lhs;
  if (ExprRefsGlobalClock(s->rhs)) return s->rhs;
  if (ExprRefsGlobalClock(s->condition)) return s->condition;
  if (ExprRefsGlobalClock(s->assert_expr)) return s->assert_expr;
  if (ExprRefsGlobalClock(s->for_cond)) return s->for_cond;
  for (const auto& ev : s->events) {
    if (ExprRefsGlobalClock(ev.signal)) return ev.signal;
  }
  return FindGlobalClockRefInSubStmts(s);
}

// True when `decl` declares a global clocking block in this scope.
bool DeclHasGlobalClocking(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      return true;
    }
  }
  return false;
}

// First $global_clock reference in a module item's slots, or nullptr.
const Expr* FindGlobalClockRefInItem(const ModuleItem* item) {
  const Expr* ref = nullptr;
  if (item->body) ref = FindGlobalClockRefInStmt(item->body);
  if (!ref && ExprRefsGlobalClock(item->init_expr)) ref = item->init_expr;
  if (!ref && ExprRefsGlobalClock(item->assign_lhs)) ref = item->assign_lhs;
  if (!ref && ExprRefsGlobalClock(item->assign_rhs)) ref = item->assign_rhs;
  if (!ref && ExprRefsGlobalClock(item->prop_body_expr)) {
    ref = item->prop_body_expr;
  }
  if (!ref) {
    for (const auto& ev : item->sensitivity) {
      if (ExprRefsGlobalClock(ev.signal)) {
        ref = ev.signal;
        break;
      }
    }
  }
  return ref;
}

// Predicate over the global clocking sampled value function kinds. Callers pass
// AcceptAnyGclk for the whole family or IsGlobalClockingFutureFunction to look
// for the future functions alone.
using GclkKindPredicate = bool (*)(GlobalClockingSampledFunction);

bool AcceptAnyGclk(GlobalClockingSampledFunction) { return true; }

// §16.9.4: recursively search `e` for the first global clocking sampled value
// function call whose kind satisfies `match`; returns that node or nullptr. The
// traversal is kept separate from the $global_clock search so the
// §14.14/§16.9.4 rules report their own diagnostics.
const Expr* FindGclkFunctionRef(const Expr* e, GclkKindPredicate match) {
  if (!e) return nullptr;
  if (e->kind == ExprKind::kSystemCall) {
    GlobalClockingSampledFunction fn{};
    if (ClassifyGlobalClockingSampledFunction(e->callee, fn) && match(fn)) {
      return e;
    }
  }
  for (const Expr* c :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->repeat_count, e->with_expr}) {
    if (const Expr* hit = FindGclkFunctionRef(c, match)) return hit;
  }
  for (auto* a : e->args) {
    if (const Expr* hit = FindGclkFunctionRef(a, match)) return hit;
  }
  for (auto* el : e->elements) {
    if (const Expr* hit = FindGclkFunctionRef(el, match)) return hit;
  }
  return nullptr;
}

const Expr* FindGclkFunctionRefInStmt(const Stmt* s, GclkKindPredicate match);

const Expr* FindGclkFunctionRefInSubStmts(const Stmt* s,
                                          GclkKindPredicate match) {
  for (auto* sub : s->stmts) {
    if (const Expr* hit = FindGclkFunctionRefInStmt(sub, match)) return hit;
  }
  if (const Expr* hit = FindGclkFunctionRefInStmt(s->then_branch, match)) {
    return hit;
  }
  if (const Expr* hit = FindGclkFunctionRefInStmt(s->else_branch, match)) {
    return hit;
  }
  if (const Expr* hit = FindGclkFunctionRefInStmt(s->body, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRefInStmt(s->for_body, match)) {
    return hit;
  }
  for (auto& ci : s->case_items) {
    if (const Expr* hit = FindGclkFunctionRefInStmt(ci.body, match)) return hit;
  }
  return nullptr;
}

const Expr* FindGclkFunctionRefInStmt(const Stmt* s, GclkKindPredicate match) {
  if (!s) return nullptr;
  if (const Expr* hit = FindGclkFunctionRef(s->expr, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(s->lhs, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(s->rhs, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(s->condition, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(s->assert_expr, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(s->for_cond, match)) return hit;
  for (const auto& ev : s->events) {
    if (const Expr* hit = FindGclkFunctionRef(ev.signal, match)) return hit;
  }
  return FindGclkFunctionRefInSubStmts(s, match);
}

// First matching global clocking sampled value function reference in a module
// item's slots, or nullptr. When `include_property_slot` is false the property
// body expression is skipped, so only the procedural / general-expression
// positions are searched (a future function is legal in a property_expr).
const Expr* FindGclkFunctionRefInItem(const ModuleItem* item,
                                      GclkKindPredicate match,
                                      bool include_property_slot) {
  if (item->body) {
    if (const Expr* hit = FindGclkFunctionRefInStmt(item->body, match)) {
      return hit;
    }
  }
  if (const Expr* hit = FindGclkFunctionRef(item->init_expr, match)) return hit;
  if (const Expr* hit = FindGclkFunctionRef(item->assign_lhs, match))
    return hit;
  if (const Expr* hit = FindGclkFunctionRef(item->assign_rhs, match))
    return hit;
  if (include_property_slot) {
    if (const Expr* hit = FindGclkFunctionRef(item->prop_body_expr, match)) {
      return hit;
    }
  }
  for (const auto& ev : item->sensitivity) {
    if (const Expr* hit = FindGclkFunctionRef(ev.signal, match)) return hit;
  }
  return nullptr;
}

}  // namespace

bool Elaborator::ModuleDeclaresGlobalClocking(const ModuleDecl* decl) {
  return DeclHasGlobalClocking(decl);
}

void Elaborator::ValidateGlobalClockReference(const ModuleDecl* decl) {
  // §14.14 lookup rules a) and b): the reference is legal when this scope, or
  // any enclosing ancestor instance up to the top-level hierarchy block,
  // declares a global clocking. global_clocking_in_scope_ (threaded through
  // ElaborateModule) already folds in this cell's own declaration, so a single
  // test covers both the local and the climbed-hierarchy cases.
  if (global_clocking_in_scope_) return;

  for (const auto* item : decl->items) {
    const Expr* ref = FindGlobalClockRefInItem(item);
    if (ref) {
      diag_.Error(ref->range.start,
                  "$global_clock has no effective global clocking declaration "
                  "in any enclosing scope up to the top-level hierarchy block",
                  Clause::Unread());
      return;
    }
  }
}

void Elaborator::ValidateGclkRequiresGlobalClocking(const ModuleDecl* decl) {
  // §16.9.4: the global clocking sampled value functions may be used only if a
  // global clocking is defined. The in-scope test mirrors the $global_clock
  // reference rule: global_clocking_in_scope_ folds this cell's own declaration
  // together with any inherited from an enclosing instance.
  if (global_clocking_in_scope_) return;

  for (const auto* item : decl->items) {
    const Expr* ref = FindGclkFunctionRefInItem(item, AcceptAnyGclk,
                                                /*include_property_slot=*/true);
    if (ref) {
      diag_.Error(ref->range.start,
                  "a global clocking sampled value function requires a global "
                  "clocking declaration in an enclosing scope",
                  Clause::Unread());
      return;
    }
  }
}

void Elaborator::ValidateFutureGclkPlacement(const ModuleDecl* decl) {
  // §16.9.4: the global clocking future sampled value functions ($future_gclk,
  // $rising_gclk, $falling_gclk, $steady_gclk, $changing_gclk) may be invoked
  // only in a property or sequence expression, so a use in procedural code, a
  // continuous assignment, an initializer, or an event control is illegal. The
  // parser does not expose property/sequence specification bodies here, so any
  // future function reachable in these procedural slots is out of place. The
  // past functions carry no such restriction and are left alone.
  for (const auto* item : decl->items) {
    const Expr* ref =
        FindGclkFunctionRefInItem(item, IsGlobalClockingFutureFunction,
                                  /*include_property_slot=*/false);
    if (ref) {
      diag_.Error(ref->range.start,
                  "a global clocking future sampled value function may appear "
                  "only in a property or sequence expression",
                  Clause::Unread());
      return;
    }
  }
}

}  // namespace delta
