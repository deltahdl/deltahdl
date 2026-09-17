#pragma once

#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

// 18.4.1: draw a value uniformly distributed over the inclusive range [lo, hi]
// read in the order a type of the given signedness reads it. Shared between
// constraint_solver.cpp (which defines it) and constraint_solver_dist.cpp.
int64_t DrawUniformInRange(bool is_signed, int64_t lo, int64_t hi,
                           std::mt19937& rng);

// 18.5.13.2: classify the active constraints into the hard relations to satisfy
// and the soft preferences to honor, omitting 'disable soft' directives (which
// are resolved separately). Walks every enabled block in declaration order and
// then the inline 'extra' constraints last, the order that fixes
// soft-constraint priority. Shared between constraint_solver_eval.cpp (which
// defines it) and constraint_solver_solve.cpp.
void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                        const std::vector<ConstraintExpr>& extra,
                        std::vector<const ConstraintExpr*>& hard,
                        std::vector<const ConstraintExpr*>& soft);

// 18.5.7.1: the count of an array's elements that take part in an iterative
// constraint over it: an array's size method is a state variable there, the
// size constraints being solved first, so only the elements whose index is
// below the size committed in `values` under `size_var` do. An empty
// size_var (a fixed-size array) leaves `count` unchanged. Shared between
// constraint_solver_eval.cpp (which defines it) and
// constraint_solver_repair.cpp.
size_t ClampCountToSize(size_t count, const std::string& size_var,
                        const std::unordered_map<std::string, int64_t>& values);

}  // namespace delta
