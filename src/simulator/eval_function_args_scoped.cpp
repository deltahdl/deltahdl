#include "simulator/eval_function_args_scoped.h"

#include <string>

#include "parser/ast_expr.h"

namespace delta {

std::string IdentifierLookupKey(const Expr* expr) {
  if (expr->scope_prefix != "$root" && expr->scope_prefix != "$unit")
    return std::string(expr->text);
  std::string key(expr->scope_prefix);
  key += '.';
  key += expr->text;
  return key;
}

std::string DeclaredKindsKey(const Expr* expr) {
  if (expr->scope_prefix == "$unit") return IdentifierLookupKey(expr);
  return std::string(expr->text);
}

}  // namespace delta
