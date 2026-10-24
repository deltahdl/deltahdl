#pragma once

#include <cstdint>
#include <vector>

#include "parser/ast_expr.h"

// Reads a declaration's unpacked dimensions back as an element count, for a
// test checking which typedef a declaration took its dimensions from.

using namespace delta;

// The element count `dims` writes where it is one dimension given as a
// number, zero otherwise.
inline uint64_t LiteralElementCount(const std::vector<Expr*>& dims) {
  if (dims.size() != 1 || dims[0]->kind != ExprKind::kIntegerLiteral) return 0;
  return dims[0]->int_val;
}
