#pragma once

#include <cstdint>
#include <string>

#include "simulator/constraint_solver.h"

using namespace delta;

// Add an integral rand variable spanning [min, max] to the solver.
inline void AddRand(ConstraintSolver& solver, const std::string& name,
                    int64_t min, int64_t max) {
  RandVariable v;
  v.name = name;
  v.min_val = min;
  v.max_val = max;
  solver.AddVariable(v);
}

// Fill a caller-owned inner/soft pair so that 'soft' is a soft constraint
// wrapping the equality "var == val". The caller owns both objects so the
// soft wrapper's inner pointer stays valid for the lifetime of the solve.
inline void MakeSoftEq(ConstraintExpr& inner, ConstraintExpr& soft,
                       const std::string& var, int64_t val) {
  inner.kind = ConstraintKind::kEqual;
  inner.var_name = var;
  inner.lo = val;
  soft.kind = ConstraintKind::kSoft;
  soft.var_name = var;
  soft.inner = &inner;
}
