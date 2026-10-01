#include "simulator/checker_actuals.h"

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "elaborator/assertion_body_slots.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assertion_read_names.h"
#include "simulator/expr_walk.h"

namespace delta {

namespace {

// What a qualified copy needs: the parent's prefix, the locals left alone
// and the arena the copy is made in.
struct Qualifying {
  const std::string& prefix;
  const std::unordered_set<std::string_view>& locals;
  Arena& arena;
};

// §23.6: whether the identifier `e` is a simple name the qualifying rewrites,
// rather than one written from a scope, a dotted path, a system name or `$`,
// or a local of the actual.
bool IsSimpleName(const Expr* e, const Qualifying& q) {
  return e->scope_prefix.empty() &&
         e->text.find('.') == std::string_view::npos &&
         !e->text.starts_with('$') && q.locals.count(e->text) == 0;
}

// A copy of `e` with each simple name written as `$root` followed by the
// parent's prefix and the name, as §23.6 has a name from the top of the
// design; a member access's member is left, as it names no object of the
// scope.
Expr* Qualified(const Expr* e, const Qualifying& q) {
  if (e == nullptr) return nullptr;
  auto* copy = q.arena.Create<Expr>(*e);
  if (e->kind == ExprKind::kIdentifier) {
    if (IsSimpleName(e, q)) {
      copy->scope_prefix = "$root";
      copy->text =
          *q.arena.Create<std::string>(q.prefix + std::string(e->text));
    }
    return copy;
  }
  copy->lhs = Qualified(e->lhs, q);
  if (e->kind != ExprKind::kMemberAccess) copy->rhs = Qualified(e->rhs, q);
  copy->base = Qualified(e->base, q);
  copy->index = Qualified(e->index, q);
  copy->index_end = Qualified(e->index_end, q);
  copy->condition = Qualified(e->condition, q);
  copy->true_expr = Qualified(e->true_expr, q);
  copy->false_expr = Qualified(e->false_expr, q);
  copy->repeat_count = Qualified(e->repeat_count, q);
  copy->with_expr = Qualified(e->with_expr, q);
  for (Expr*& arg : copy->args) arg = Qualified(arg, q);
  for (Expr*& element : copy->elements) element = Qualified(element, q);
  return copy;
}

// A copy of the tree under `node` whose nodes and sequences are its own, so
// that its expressions can be rewritten for one instance.
PropertyExprNode* CopiedTree(const PropertyExprNode* node, Arena& arena) {
  auto* copy = arena.Create<PropertyExprNode>(*node);
  if (node->sequence != nullptr) {
    copy->sequence = arena.Create<ModuleItem>(*node->sequence);
  }
  for (PropertyExprNode*& operand : copy->operands) {
    operand = CopiedTree(operand, arena);
  }
  return copy;
}

}  // namespace

Expr* ActualInInstantiatingScope(Expr* actual, const std::string& parent_prefix,
                                 Arena& arena) {
  if (actual == nullptr ||
      (actual->property_actual == nullptr && !IsEventActual(actual))) {
    return actual;
  }
  std::unordered_set<std::string_view> locals;
  const Qualifying kQ{parent_prefix, locals, arena};
  if (actual->property_actual == nullptr) return Qualified(actual, kQ);
  CollectTreeLocals(actual->property_actual, locals);
  auto* copy = arena.Create<Expr>(*actual);
  copy->property_actual = CopiedTree(actual->property_actual, arena);
  ForEachTreeSlot(copy->property_actual,
                  [&kQ](Expr*& e) { e = Qualified(e, kQ); });
  return copy;
}

Expr* ProceduralActualInInstantiatingScope(
    Expr* actual, const std::string& parent_prefix,
    const std::vector<std::string_view>& locals, Arena& arena) {
  if (actual == nullptr || actual->property_actual != nullptr ||
      IsEventActual(actual)) {
    return nullptr;
  }
  std::unordered_set<std::string_view> bare(locals.begin(), locals.end());
  bool saved = false;
  ForEachSubExpr(actual, [&](const Expr* sub) {
    saved = saved || (sub->kind == ExprKind::kCast && sub->text == "const") ||
            (sub->kind == ExprKind::kIdentifier && sub->scope_prefix.empty() &&
             bare.count(sub->text) != 0);
  });
  if (!saved) return nullptr;
  return Qualified(actual, {parent_prefix, bare, arena});
}

void SubstituteActualsInAssertion(Stmt& stmt, const ActualsByFormal& actuals,
                                  Arena& arena) {
  auto substitute = [&](Expr*& e) { e = SubstituteFormals(e, actuals, arena); };
  substitute(stmt.assert_expr);
  substitute(stmt.assert_disable_iff);
  if (stmt.assert_property != nullptr) {
    stmt.assert_property = CopiedTree(stmt.assert_property, arena);
    ForEachTreeSlot(stmt.assert_property, substitute);
  }
  if (stmt.assert_sequence != nullptr) {
    stmt.assert_sequence = arena.Create<ModuleItem>(*stmt.assert_sequence);
    ForEachBodySlot(stmt.assert_sequence->seq_linear, substitute);
  }
}

void CollectActualReadNames(Expr* actual,
                            std::unordered_set<std::string>& out) {
  if (actual == nullptr || actual->property_actual == nullptr) return;
  ForEachTreeSlot(actual->property_actual,
                  [&out](Expr*& e) { CollectSampledOperandNames(e, out); });
}

}  // namespace delta
