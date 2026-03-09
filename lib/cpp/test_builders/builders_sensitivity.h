#pragma once

#include "builders_ast.h"

// Convenience aliases for sensitivity-analysis tests.
inline Expr* SensId(Arena& arena, std::string_view name) {
  return MakeId(arena, name);
}

inline Expr* SensIntLit(Arena& arena, uint64_t val) {
  return MakeInt(arena, val);
}

inline Expr* SensSelect(Arena& arena, Expr* base, Expr* index) {
  return MakeSelectExpr(arena, base, index);
}
