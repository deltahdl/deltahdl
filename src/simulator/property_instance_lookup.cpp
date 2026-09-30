#include <functional>
#include <string>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/property_attempts.h"
#include "simulator/sim_context.h"

// §16.12.17 and §16.12.18: what the tree evaluator asks of an instance of
// a named property among its booleans, the declaration it names and the
// sequences and properties it takes as actuals, split out of
// property_attempts.cpp.

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

}  // namespace delta
