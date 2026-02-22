// §18.12: Randomization of scope variables—std::randomize()

#include "simulation/constraint_solver.h"
#include <algorithm>
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// §18.11: std::randomize() standalone function
// =============================================================================
TEST(Constraint, StdRandomizeStandalone) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "local_var";
  v.min_val = 0;
  v.max_val = 255;
  solver.AddVariable(v);

  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "local_var";
  c.lo = 100;
  c.hi = 200;

  ASSERT_TRUE(solver.SolveWith({c}));
  int64_t val = solver.GetValue("local_var");
  EXPECT_GE(val, 100);
  EXPECT_LE(val, 200);
}

} // namespace
