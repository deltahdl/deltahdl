#pragma once

#include <cstdint>
#include <vector>

#include "parser/ast_expr.h"

using namespace delta;

inline uint64_t LiteralElementCount(const std::vector<Expr*>& dims) {
  if (dims.size() != 1 || dims[0]->kind != ExprKind::kIntegerLiteral) return 0;
  return dims[0]->int_val;
}
