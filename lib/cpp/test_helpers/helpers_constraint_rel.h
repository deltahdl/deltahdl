#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>

#include "simulator/constraint_solver.h"

using namespace delta;

// Adds a custom constraint block "c_rel" expressing the relation x == y + 1 to
// the given solver. Used by rand_mode()/inline randomize() tests that solve an
// active variable "x" against a held state variable "y".
inline void AddXEqualsYPlusOneConstraint(ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = "c_rel";
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto itx = vals.find("x");
    auto ity = vals.find("y");
    if (itx == vals.end() || ity == vals.end()) return true;
    return itx->second == ity->second + 1;
  };
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);
}
