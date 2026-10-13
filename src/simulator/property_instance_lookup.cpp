#include <functional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/property_attempts.h"
#include "simulator/sim_context.h"

// §16.12.17 and §16.12.18: what the tree evaluator asks of an instance of
// a named property among its booleans, the declaration it names, the
// sequences and properties it takes as actuals, and the declaration's tree
// with those actuals substituted, split out of property_attempts.cpp.

namespace delta {

void ForEachPropertyActual(
    const Expr* instance,
    const std::function<void(const PropertyExprNode*)>& fn) {
  if (instance == nullptr || instance->kind != ExprKind::kCall) return;
  for (const Expr* arg : instance->args) {
    if (arg != nullptr && arg->property_actual != nullptr) {
      fn(arg->property_actual);
    }
  }
}

const ModuleItem* InstantiatedProperty(const Expr* instance, SimContext& ctx) {
  std::string name = InstanceDeclName(instance);
  if (name.empty()) return nullptr;
  const ModuleItem* decl = ctx.FindPropertyDecl(name);
  if (decl == nullptr || decl->prop_body_tree == nullptr) return nullptr;
  return decl;
}

namespace {

// §16.12.18: the tree the actual of a formal carries where `e` references
// the formal and the actual is a sequence_expr or a property_expr; nullptr
// for any other expression.
const PropertyExprNode* ActualProperty(const Expr* e,
                                       const ActualsByFormal& actuals) {
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return nullptr;
  auto it = actuals.find(e->text);
  if (it == actuals.end() || it->second == nullptr) return nullptr;
  return it->second->property_actual;
}

}  // namespace

// §16.12.18: the sequences and properties passed as actuals to an instance
// in the body read the formals as the body's expressions do, so the tree
// each such argument carries is substituted too; the argument is the copy
// the expression substitution made.
void SubstituteActualProperties(Expr* instance, const ActualsByFormal& actuals,
                                Arena& arena) {
  if (instance == nullptr || instance->kind != ExprKind::kCall ||
      actuals.empty()) {
    return;
  }
  for (Expr* arg : instance->args) {
    if (arg != nullptr && arg->property_actual != nullptr) {
      arg->property_actual =
          SubstituteTree(arg->property_actual, actuals, arena);
    }
  }
}

// §F.4.1: a copy of the tree under `node` with the actuals substituted for
// the formals in every expression it holds; a sequence is shared with the
// original and substituted where it is flattened. §16.12.18: a boolean
// operand that references a formal whose actual is a sequence_expr or a
// property_expr stands for the actual, copied so that its nodes are the
// expansion's own.
PropertyExprNode* SubstituteTree(const PropertyExprNode* node,
                                 const ActualsByFormal& actuals, Arena& arena) {
  if (node->kind == PropertyExprNode::Kind::kBoolean) {
    if (const PropertyExprNode* actual =
            ActualProperty(node->boolean, actuals)) {
      return SubstituteTree(actual, ActualsByFormal{}, arena);
    }
  }
  auto* copy = arena.Create<PropertyExprNode>(*node);
  copy->boolean = SubstituteFormals(node->boolean, actuals, arena);
  SubstituteActualProperties(copy->boolean, actuals, arena);
  copy->range_min = SubstituteFormals(node->range_min, actuals, arena);
  copy->range_max = SubstituteFormals(node->range_max, actuals, arena);
  for (std::vector<Expr*>& values : copy->case_values) {
    for (Expr*& value : values) {
      value = SubstituteFormals(value, actuals, arena);
    }
  }
  copy->operands.clear();
  for (const PropertyExprNode* operand : node->operands) {
    copy->operands.push_back(SubstituteTree(operand, actuals, arena));
  }
  return copy;
}

}  // namespace delta
