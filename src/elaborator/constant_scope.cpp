#include "elaborator/constant_scope.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/const_eval.h"
#include "parser/ast_stmt.h"

namespace delta {

void ConstantScope::Declare(std::string_view name, const Expr* value) {
  std::optional<int64_t> folded = ConstEvalInt(value, fold);
  if (folded) {
    fold[name] = *folded;
  } else {
    fold.erase(name);
  }
  constants[name] = folded.value_or(0);
}

bool DeclaresParam(const Stmt* stmt) {
  return stmt->kind == StmtKind::kVarDecl && stmt->var_is_param;
}

bool BlockDeclaresParam(const Stmt& stmt) {
  for (const std::vector<Stmt*>* items : {&stmt.stmts, &stmt.fork_stmts}) {
    if (std::any_of(items->begin(), items->end(), DeclaresParam)) return true;
  }
  return false;
}

}  // namespace delta
