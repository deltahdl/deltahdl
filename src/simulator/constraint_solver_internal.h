#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
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

// The domain of `var` narrowed by the comparison `sub`, its bounds folded
// as a comparison against a constant folds them before the draw, and
// whether a constraint kind is such a comparison. Shared between
// constraint_solver_repair.cpp (which defines them) and
// constraint_solver_solve.cpp.
RandVariable Narrowed(const RandVariable& var, const ConstraintExpr& sub);
bool IsComparison(ConstraintKind kind);
// The comparison `kind` as read from its other side, x < y read as y > x.
// Shared between constraint_solver_propagate.cpp (which defines it) and
// constraint_solver_repair.cpp.
ConstraintKind MirrorComparisonKind(ConstraintKind kind);

// Seeds a single concrete constraint directly into `values`: an equality
// fixes the variable to its constant and a set membership picks one of the
// listed values at random; a variable holding a state value is never
// seeded. Shared between constraint_solver_solve.cpp (which defines it) and
// constraint_solver_soft.cpp.
void ApplyConcreteConstraint(const ConstraintExpr& c,
                             std::unordered_map<std::string, int64_t>& values,
                             std::mt19937& rng, bool holds_state_value);

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

// 18.8 / 18.5.8: an inactive variable (rand_mode() OFF) is not one of the
// active random variables, so it is not randomized. The solver instead seeds
// its current value as a constant before solving (the real value into
// 'real_values', the integral value into 'values') so a global constraint
// relating it to an active variable is evaluated against that fixed value
// rather than dropped. Shared between constraint_solver_solve.cpp (which
// defines it) and constraint_solver_sizes.cpp.
void SeedInactiveVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    std::unordered_map<std::string, double>& real_values);

// 18.5.7.1: an array's size method is solved with the size constraints, ahead
// of the iterative (foreach) constraints over that array. Commits every
// active, non-randc, still-uncommitted array-size variable so a foreach
// reading the size sees the chosen value and treats it as a state variable.
// Shared between constraint_solver_sizes.cpp (which defines it) and
// constraint_solver_solve.cpp.
void DrawArraySizeVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    const std::function<int64_t(RandVariable&)>& gen);

// Whether the constraint `c` names the variable `name`, as the variable it
// constrains or among the ones it references, and no other random variable,
// so that it can be decided on that variable's value alone. Shared between
// constraint_solver_dist.cpp (which defines it) and
// constraint_solver_solve.cpp.
bool ConfinedTo(const ConstraintExpr& c, const std::string& name);

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
