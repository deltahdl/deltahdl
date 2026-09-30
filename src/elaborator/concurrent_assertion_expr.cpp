#include "elaborator/concurrent_assertion_expr.h"

#include <string>
#include <string_view>
#include <unordered_set>

#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"

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

// The class a variable of the module holds a handle to, or nullptr where the
// variable is none or its class is not one the unit declares.
const ClassDecl* HandleClass(std::string_view name, const RtlirModule* mod,
                             const CompilationUnit* unit) {
  if (name.empty() || mod == nullptr || unit == nullptr) return nullptr;
  for (const auto& v : mod->variables) {
    if (v.name != name) continue;
    if (v.class_type_name.empty()) return nullptr;
    return FindClassDecl(v.class_type_name, unit);
  }
  return nullptr;
}

// Whether `cls`, or a class it extends (§8.13), declares `member` without
// `static`. False where no class on the chain declares it, so a name this
// cannot place is never reported.
bool DeclaresNonStaticMember(const ClassDecl* cls, std::string_view member,
                             const CompilationUnit* unit) {
  std::unordered_set<const ClassDecl*> seen;
  while (cls != nullptr && seen.insert(cls).second) {
    for (const ClassMember* m : cls->members) {
      std::string_view name = m->method != nullptr ? m->method->name : m->name;
      if (name == member) return !m->is_static;
    }
    cls = cls->base_class.empty() ? nullptr
                                  : FindClassDecl(cls->base_class, unit);
  }
  return false;
}

// Recursively searches an assertion expression for `h.m`, a property read or
// a method called through a handle `h` to an object, where `m` is a non-static
// member of the handle's class. Writes `h.m` to `out` for the first one.
bool FindNonStaticMemberRef(const Expr* e, const RtlirModule* mod,
                            const CompilationUnit* unit, std::string& out) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
      e->lhs != nullptr && e->lhs->kind == ExprKind::kIdentifier &&
      e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
      DeclaresNonStaticMember(HandleClass(e->lhs->text, mod, unit),
                              e->rhs->text, unit)) {
    out = std::string(e->lhs->text) + "." + std::string(e->rhs->text);
    return true;
  }
  const Expr* children[] = {
      e->lhs,       e->rhs,       e->base,       e->index,        e->index_end,
      e->condition, e->true_expr, e->false_expr, e->repeat_count, e->with_expr};
  for (const Expr* c : children) {
    if (FindNonStaticMemberRef(c, mod, unit, out)) return true;
  }
  for (const Expr* a : e->args) {
    if (FindNonStaticMemberRef(a, mod, unit, out)) return true;
  }
  for (const Expr* el : e->elements) {
    if (FindNonStaticMemberRef(el, mod, unit, out)) return true;
  }
  return false;
}

}  // namespace

std::string ConcurrentAssertionExprReferencedNonStaticMember(
    const Expr* body, const RtlirModule* mod, const CompilationUnit* unit) {
  std::string out;
  FindNonStaticMemberRef(body, mod, unit, out);
  return out;
}

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
