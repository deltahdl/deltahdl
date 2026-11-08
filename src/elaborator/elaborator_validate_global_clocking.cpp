#include <vector>

#include "common/diagnostic.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clocking_declaration.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

void Elaborator::ValidateDuplicateGlobalClocking(const ModuleDecl* decl) {
  const ModuleItem* first_global = nullptr;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      if (first_global) {
        diag_.Error(item->loc,
                    "only one global clocking block is allowed per scope",
                    Subclause("14.14"));
        return;
      }
      first_global = item;
    }
  }
}

namespace {

bool ExprRefsGlobalClock(const Expr* e);

bool AnyScalarChildRefsGlobalClock(const Expr* e) {
  for (const Expr* child : {e->lhs, e->rhs, e->condition, e->true_expr,
                            e->false_expr, e->base, e->index, e->index_end,
                            e->repeat_count, e->with_expr, e->stream_range}) {
    if (ExprRefsGlobalClock(child)) return true;
  }
  return false;
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

const Expr* FindGlobalClockRefInSubStmts(const Stmt* s) {
  const Expr* found = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = FindGlobalClockRefInStmt(sub);
  });
  return found;
}

const Expr* FindGlobalClockRefInOwnExprs(const Stmt* s) {
  const Expr* found = nullptr;
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (found) return;
    if (ExprRefsGlobalClock(e)) found = e;
  });
  return found;
}

const Expr* FindGlobalClockRefInStmt(const Stmt* s) {
  if (!s) return nullptr;
  if (const Expr* hit = FindGlobalClockRefInOwnExprs(s)) return hit;
  return FindGlobalClockRefInSubStmts(s);
}

bool DeclHasGlobalClocking(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking) {
      return true;
    }
  }
  return false;
}

static const Expr* FindGlobalClockRefInSensitivity(
    const std::vector<EventExpr>& sensitivity) {
  for (const auto& ev : sensitivity) {
    if (ExprRefsGlobalClock(ev.signal)) return ev.signal;
    if (ExprRefsGlobalClock(ev.iff_condition)) return ev.iff_condition;
  }
  return nullptr;
}

const Expr* FindGlobalClockRefInItem(const ModuleItem* item) {
  const Expr* ref = nullptr;
  if (item->body) ref = FindGlobalClockRefInStmt(item->body);
  if (!ref && ExprRefsGlobalClock(item->init_expr)) ref = item->init_expr;
  if (!ref && ExprRefsGlobalClock(item->assign_lhs)) ref = item->assign_lhs;
  if (!ref && ExprRefsGlobalClock(item->assign_rhs)) ref = item->assign_rhs;
  if (!ref && ExprRefsGlobalClock(item->prop_body_expr)) {
    ref = item->prop_body_expr;
  }
  if (!ref) ref = FindGlobalClockRefInSensitivity(item->sensitivity);
  return ref;
}

bool AcceptAnyGclk(GlobalClockingSampledFunction) { return true; }

const Expr* FindGclkFunctionRef(const Expr* e, GclkKindPredicate match) {
  if (!e) return nullptr;
  if (e->kind == ExprKind::kSystemCall) {
    GlobalClockingSampledFunction fn{};
    if (ClassifyGlobalClockingSampledFunction(e->callee, fn) && match(fn)) {
      return e;
    }
  }
  for (const Expr* c : {e->lhs, e->rhs, e->condition, e->true_expr,
                        e->false_expr, e->base, e->index, e->index_end,
                        e->repeat_count, e->with_expr, e->stream_range}) {
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

const Expr* FindGclkFunctionRefInStmt(const Stmt* s, GclkKindPredicate match,
                                      bool include_property_slot);

const Expr* FindGclkFunctionRefInSubStmts(const Stmt* s,
                                          GclkKindPredicate match,
                                          bool include_property_slot) {
  const Expr* found = nullptr;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = FindGclkFunctionRefInStmt(sub, match, include_property_slot);
  });
  return found;
}

const Expr* PropertySlotOfStmt(const Stmt* s) {
  return s->is_concurrent_clocked ? s->assert_expr : nullptr;
}

const Expr* FindGclkFunctionRefInPropertyShapes(const Stmt* s,
                                                GclkKindPredicate match) {
  const Expr* found = nullptr;
  auto search = [&](const Expr* e) {
    if (found == nullptr) found = FindGclkFunctionRef(e, match);
  };
  ForEachTreeExpr(s->assert_property, search);
  if (s->assert_sequence != nullptr) {
    ForEachBodyExpr(s->assert_sequence->seq_linear, search);
  }
  return found;
}

const Expr* FindGclkFunctionRefInOwnExprs(const Stmt* s,
                                          GclkKindPredicate match,
                                          bool include_property_slot) {
  const Expr* skip = include_property_slot ? nullptr : PropertySlotOfStmt(s);
  const Expr* found = nullptr;
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (found || (skip != nullptr && e == skip)) return;
    found = FindGclkFunctionRef(e, match);
  });
  if (found == nullptr && include_property_slot) {
    found = FindGclkFunctionRefInPropertyShapes(s, match);
  }
  return found;
}

const Expr* FindGclkFunctionRefInStmt(const Stmt* s, GclkKindPredicate match,
                                      bool include_property_slot) {
  if (!s) return nullptr;
  if (const Expr* hit =
          FindGclkFunctionRefInOwnExprs(s, match, include_property_slot)) {
    return hit;
  }
  return FindGclkFunctionRefInSubStmts(s, match, include_property_slot);
}

}  // namespace

const Expr* FindGclkFunctionRefInItem(const ModuleItem* item,
                                      GclkKindPredicate match,
                                      bool include_property_slot) {
  if (item->body) {
    if (const Expr* hit = FindGclkFunctionRefInStmt(item->body, match,
                                                    include_property_slot)) {
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
    if (const Expr* hit = FindGclkFunctionRef(ev.iff_condition, match)) {
      return hit;
    }
  }
  return nullptr;
}

bool ModuleDeclaresGlobalClocking(const ModuleDecl* decl) {
  return DeclHasGlobalClocking(decl);
}

const std::vector<EventExpr>* ModuleGlobalClockingEvent(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking && !item->clocking_event.empty()) {
      return &item->clocking_event;
    }
  }
  return nullptr;
}

void Elaborator::ValidateGlobalClockReference(const ModuleDecl* decl) {
  if (global_clocking_in_scope_) return;

  for (const auto* item : decl->items) {
    const Expr* ref = FindGlobalClockRefInItem(item);
    if (ref) {
      diag_.Error(ref->range.start,
                  "$global_clock has no effective global clocking declaration "
                  "in any enclosing scope up to the top-level hierarchy block",
                  Subclause("14.14"));
      return;
    }
  }
}

void Elaborator::ValidateGclkRequiresGlobalClocking(const ModuleDecl* decl) {
  if (global_clocking_in_scope_) return;

  for (const auto* item : decl->items) {
    const Expr* ref = FindGclkFunctionRefInItem(item, AcceptAnyGclk, true);
    if (ref) {
      diag_.Error(ref->range.start,
                  "a global clocking sampled value function requires a global "
                  "clocking declaration in an enclosing scope",
                  Subclause("16.9.4"));
      return;
    }
  }
}

void Elaborator::ValidateFutureGclkPlacement(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    const Expr* ref =
        FindGclkFunctionRefInItem(item, IsGlobalClockingFutureFunction, false);
    if (ref) {
      diag_.Error(ref->range.start,
                  "a global clocking future sampled value function may appear "
                  "only in a property or sequence expression",
                  Subclause("16.9.4"));
      return;
    }
  }
}

}  // namespace delta
