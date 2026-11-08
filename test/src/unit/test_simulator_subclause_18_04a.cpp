#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_set>
#include <vector>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

TEST(Constraint, RandVariableBasic) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.qualifier = RandQualifier::kRand;
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 100);
}

TEST(Constraint, RandVariableMultiple) {
  ConstraintSolver solver(42);
  for (const auto& name : {"a", "b", "c"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 255;
    solver.AddVariable(v);
  }
  ASSERT_TRUE(solver.Solve());
  for (const auto& name : {"a", "b", "c"}) {
    int64_t val = solver.GetValue(name);
    EXPECT_GE(val, 0);
    EXPECT_LE(val, 255);
  }
}

TEST(Constraint, RandcCyclic) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.qualifier = RandQualifier::kRandc;
  v.min_val = 0;
  v.max_val = 3;
  solver.AddVariable(v);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    seen.insert(solver.GetValue("x"));
  }
  EXPECT_EQ(seen.size(), 4u);
}

TEST(Constraint, EnumMemberExceptionLiftsRestriction) {
  ConstraintSolver solver(5);
  RandVariable v;
  v.name = "m";
  v.min_val = 0;
  v.max_val = 15;
  v.enum_values = {1, 4, 9};
  v.apply_enum_restriction = false;
  solver.AddVariable(v);

  std::unordered_set<int64_t> seen;
  bool saw_non_named = false;
  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t val = solver.GetValue("m");
    EXPECT_GE(val, 0);
    EXPECT_LE(val, 15);
    seen.insert(val);
    if (val != 1 && val != 4 && val != 9) saw_non_named = true;
  }
  EXPECT_TRUE(saw_non_named);
}

TEST(Constraint, EnumRestrictionConfinesByDefault) {
  ConstraintSolver solver(5);
  RandVariable v;
  v.name = "m";
  v.min_val = 0;
  v.max_val = 15;
  v.enum_values = {1, 4, 9};
  solver.AddVariable(v);

  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t val = solver.GetValue("m");
    EXPECT_TRUE(val == 1 || val == 4 || val == 9);
  }
}

TEST(Constraint, RandcCycleResets) {
  ConstraintSolver solver(123);
  RandVariable v;
  v.name = "y";
  v.qualifier = RandQualifier::kRandc;
  v.min_val = 0;
  v.max_val = 1;
  solver.AddVariable(v);

  std::unordered_set<int64_t> cycle1;
  for (int i = 0; i < 2; ++i) {
    ASSERT_TRUE(solver.Solve());
    cycle1.insert(solver.GetValue("y"));
  }
  EXPECT_EQ(cycle1.size(), 2u);

  std::unordered_set<int64_t> cycle2;
  for (int i = 0; i < 2; ++i) {
    ASSERT_TRUE(solver.Solve());
    cycle2.insert(solver.GetValue("y"));
  }
  EXPECT_EQ(cycle2.size(), 2u);
}

TEST(RandomVariableTypes, RandomizeLeavesObjectHandleUnmodified) {
  const char* src =
      "class Inner;\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner child;\n"
      "  rand int a;\n"
      "  constraint c { a > 0; a < 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int seen;\n"
      "  initial begin\n"
      "    static Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    seen = (o.child == null) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "seen"), 1u);
}

}  // namespace
