#include "elaborator/concurrent_assertion_expr.h"

#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

// True when `name` is declared as a chandle variable of the module.
bool NamesChandleVariable(std::string_view name, const RtlirModule* mod) {
  if (name.empty() || mod == nullptr) return false;
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.is_chandle;
  }
  return false;
}

// Recursively searches an assertion expression for a reference to a chandle
// variable. Returns the first such variable's name, or an empty view.
std::string_view FindChandleRef(const Expr* e, const RtlirModule* mod) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier && NamesChandleVariable(e->text, mod)) {
    return e->text;
  }
  const Expr* children[] = {
      e->lhs,       e->rhs,       e->base,       e->index,        e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count, e->with_expr};
  for (const Expr* c : children) {
    auto hit = FindChandleRef(c, mod);
    if (!hit.empty()) return hit;
  }
  for (const Expr* a : e->args) {
    auto hit = FindChandleRef(a, mod);
    if (!hit.empty()) return hit;
  }
  for (const Expr* el : e->elements) {
    auto hit = FindChandleRef(el, mod);
    if (!hit.empty()) return hit;
  }
  return {};
}

}  // namespace

std::string_view ConcurrentAssertionExprReferencedChandle(
    const Expr* body, const RtlirModule* mod) {
  return FindChandleRef(body, mod);
}

bool ConcurrentAssertionExprTypeIsAcceptable(bool overall_result_castable) {
  return overall_result_castable;
}

bool ConcurrentAssertionSubexprTypeIsExempt() {
  // §16.6 carves out subexpressions explicitly: only the overall expression
  // must be cast compatible with an integral type.
  return true;
}

bool AutomaticVariableReferenceAllowed(
    bool inside_procedural_concurrent_assertion) {
  return inside_procedural_concurrent_assertion;
}

bool NonStaticClassMemberReferenceAllowed() { return false; }

bool ChandleVariableReferenceAllowed() { return false; }

bool SideEffectAllowed(bool inside_sequence_match_item,
                       bool variable_lvalue_is_local) {
  return inside_sequence_match_item && variable_lvalue_is_local;
}

bool FunctionArgKindAllowedInAssertionExpr(FunctionArgKind kind) {
  switch (kind) {
    case FunctionArgKind::kInput:
    case FunctionArgKind::kConstRef:
      return true;
    case FunctionArgKind::kOutput:
    case FunctionArgKind::kInout:
    case FunctionArgKind::kRef:
      return false;
  }
  return false;
}

bool FunctionEligibleInAssertionExpr(bool is_automatic, bool preserves_no_state,
                                     bool has_no_side_effects) {
  // §16.6 phrases the lifetime constraint as automatic OR stateless: a static
  // function with no preserved state is acceptable in lieu of an automatic
  // one. The no-side-effects requirement is independent and always required.
  return (is_automatic || preserves_no_state) && has_no_side_effects;
}

bool DisableConditionRefAllowed(DisableConditionRefKind kind) {
  switch (kind) {
    case DisableConditionRefKind::kOrdinaryVariable:
    case DisableConditionRefKind::kTriggeredMethod:
      return true;
    case DisableConditionRefKind::kLocalVariable:
    case DisableConditionRefKind::kMatchedMethod:
      return false;
  }
  return false;
}

}  // namespace delta
