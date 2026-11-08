#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <unordered_set>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

RandVariable MakeRandc(const char* name, int64_t lo, int64_t hi) {
  RandVariable v;
  v.name = name;
  v.qualifier = RandQualifier::kRandc;
  v.min_val = lo;
  v.max_val = hi;
  return v;
}

TEST(RandcModifierCyclic, PermutationContainsOnlyTwoStateValues) {
  ConstraintSolver solver(9);
  solver.AddVariable(MakeRandc("x", 0, 7));

  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 7);
  }
}

TEST(RandcModifierCyclic, EightBitRandcCoversEntireRangeInOneIteration) {
  ConstraintSolver solver(3);
  solver.AddVariable(MakeRandc("x", 0, 255));

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 256; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 255);
    EXPECT_TRUE(seen.insert(v).second) << "value " << v << " repeated";
  }
  EXPECT_EQ(seen.size(), 256u);
}

TEST(RandcModifierCyclic, ConstrainedRandcYieldsOnlySatisfyingValues) {
  ConstraintSolver solver(11);
  solver.AddVariable(MakeRandc("x", 0, 3));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr lt;
  lt.kind = ConstraintKind::kLessThan;
  lt.var_name = "x";
  lt.lo = 2;
  block.constraints.push_back(lt);
  solver.AddConstraintBlock(block);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 40; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    EXPECT_LT(v, 2) << "constraint-violating value produced";
    EXPECT_GE(v, 0);
    seen.insert(v);
  }
  EXPECT_EQ(seen.count(0), 1u);
  EXPECT_EQ(seen.count(1), 1u);
}

TEST(RandcModifierCyclic, PermutationRecomputedWhenConstraintsChange) {
  ConstraintSolver solver(41);
  solver.AddVariable(MakeRandc("x", 0, 3));

  for (int i = 0; i < 3; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 3);
  }

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr ge;
  ge.kind = ConstraintKind::kGreaterEqual;
  ge.var_name = "x";
  ge.lo = 2;
  block.constraints.push_back(ge);
  solver.AddConstraintBlock(block);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 30; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    EXPECT_GE(v, 2) << "value from the stale pre-change permutation produced";
    EXPECT_LE(v, 3);
    seen.insert(v);
  }
  EXPECT_EQ(seen.count(2), 1u);
  EXPECT_EQ(seen.count(3), 1u);
}

TEST(RandcModifierCyclic, DegenerateSingleValueRangeAlwaysYieldsThatValue) {
  ConstraintSolver solver(2);
  solver.AddVariable(MakeRandc("x", 7, 7));

  for (int i = 0; i < 16; ++i) {
    ASSERT_TRUE(solver.Solve());
    EXPECT_EQ(solver.GetValue("x"), 7);
  }
}

TEST(RandcModifierCyclic, PermutationCoversNonZeroBasedRange) {
  ConstraintSolver solver(17);
  solver.AddVariable(MakeRandc("x", 5, 8));

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 5);
    ASSERT_LE(v, 8);
    EXPECT_TRUE(seen.insert(v).second) << "value " << v << " repeated";
  }
  EXPECT_EQ(seen.size(), 4u);
  EXPECT_EQ(seen.count(5), 1u);
  EXPECT_EQ(seen.count(6), 1u);
  EXPECT_EQ(seen.count(7), 1u);
  EXPECT_EQ(seen.count(8), 1u);
}

TEST(RandcModifierCyclic, UnsatisfiableConstraintFailsRandomize) {
  ConstraintSolver solver(23);
  solver.AddVariable(MakeRandc("x", 0, 3));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr gt;
  gt.kind = ConstraintKind::kGreaterThan;
  gt.var_name = "x";
  gt.lo = 5;
  block.constraints.push_back(gt);
  solver.AddConstraintBlock(block);

  for (int i = 0; i < 4; ++i) {
    EXPECT_FALSE(solver.Solve());
  }
}

TEST(RandcModifierCyclic, StaticRandcSharesOneCycleAcrossInstances) {
  auto shared = std::make_shared<std::unordered_set<int64_t>>();

  auto make_static = [&](const char* name) {
    RandVariable v = MakeRandc(name, 0, 3);
    v.is_static = true;
    v.shared_randc_state = shared;
    return v;
  };

  ConstraintSolver inst_a(31);
  ConstraintSolver inst_b(37);
  inst_a.AddVariable(make_static("x"));
  inst_b.AddVariable(make_static("x"));

  std::unordered_set<int64_t> seen;
  ConstraintSolver* order[] = {&inst_a, &inst_b, &inst_a, &inst_b};
  for (ConstraintSolver* s : order) {
    ASSERT_TRUE(s->Solve());
    int64_t v = s->GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 3);
    EXPECT_TRUE(seen.insert(v).second)
        << "value " << v << " repeated across instances of a static randc";
  }
  EXPECT_EQ(seen.size(), 4u);
}

TEST(RandcModifierCyclicFromSource,
     DeclaredRandcCyclesWithoutRepeatAcrossCalls) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3, v4, v5, v6, v7;\n"
      "    int ok;\n"
      "    static C o = new;\n"
      "    ok = o.randomize(); v0 = o.y;\n"
      "    ok = o.randomize(); v1 = o.y;\n"
      "    ok = o.randomize(); v2 = o.y;\n"
      "    ok = o.randomize(); v3 = o.y;\n"
      "    ok = o.randomize(); v4 = o.y;\n"
      "    ok = o.randomize(); v5 = o.y;\n"
      "    ok = o.randomize(); v6 = o.y;\n"
      "    ok = o.randomize(); v7 = o.y;\n"
      "    good = ((v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "            (v1 != v2) && (v1 != v3) && (v2 != v3) &&\n"
      "            (v4 != v5) && (v4 != v6) && (v4 != v7) &&\n"
      "            (v5 != v6) && (v5 != v7) && (v6 != v7)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandcModifierCyclicFromSource, RandcCyclesUndisturbedByCoexistingRand) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] r;\n"
      "  rand bit [7:0] a;\n"
      "  constraint ca { a < 200; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int r0, r1, r2, r3;\n"
      "    int a_ok;\n"
      "    int ok;\n"
      "    static C o = new;\n"
      "    a_ok = 1;\n"
      "    ok = o.randomize(); r0 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r1 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r2 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r3 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    good = (a_ok && (r0 != r1) && (r0 != r2) && (r0 != r3) &&\n"
      "            (r1 != r2) && (r1 != r3) && (r2 != r3)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandcModifierCyclicFromSource,
     ConstrainedRandcYieldsOnlyAdmissibleValues) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] x;\n"
      "  constraint c { x < 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int in_range;\n"
      "    int saw0, saw1;\n"
      "    int ok;\n"
      "    static C o = new;\n"
      "    in_range = 1;\n"
      "    saw0 = 0;\n"
      "    saw1 = 0;\n"
      "    for (int i = 0; i < 6; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x >= 2) in_range = 0;\n"
      "      if (o.x == 0) saw0 = 1;\n"
      "      if (o.x == 1) saw1 = 1;\n"
      "    end\n"
      "    good = (in_range && saw0 && saw1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandcModifierCyclicFromSource,
     EightBitRandcIsSupportedAndCyclesOverRange) {
  const char* src =
      "class C;\n"
      "  randc bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3, v4, v5, v6, v7;\n"
      "    int in_range;\n"
      "    int ok;\n"
      "    static C o = new;\n"
      "    in_range = 1;\n"
      "    ok = o.randomize(); v0 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v1 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v2 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v3 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v4 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v5 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v6 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v7 = o.x; if (o.x > 255) in_range = 0;\n"
      "    good = (in_range &&\n"
      "            (v0 != v1) && (v0 != v2) && (v0 != v3) && (v0 != v4) &&\n"
      "            (v0 != v5) && (v0 != v6) && (v0 != v7) && (v1 != v2) &&\n"
      "            (v1 != v3) && (v1 != v4) && (v1 != v5) && (v1 != v6) &&\n"
      "            (v1 != v7) && (v2 != v3) && (v2 != v4) && (v2 != v5) &&\n"
      "            (v2 != v6) && (v2 != v7) && (v3 != v4) && (v3 != v5) &&\n"
      "            (v3 != v6) && (v3 != v7) && (v4 != v5) && (v4 != v6) &&\n"
      "            (v4 != v7) && (v5 != v6) && (v5 != v7) && (v6 != v7))\n"
      "           ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandcModifierCyclicFromSource, StaticRandcSharesOneCycleAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static randc bit [1:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3;\n"
      "    int ok;\n"
      "    static C a = new;\n"
      "    static C b = new;\n"
      "    ok = a.randomize(); v0 = a.x;\n"
      "    ok = b.randomize(); v1 = b.x;\n"
      "    ok = a.randomize(); v2 = a.x;\n"
      "    ok = b.randomize(); v3 = b.x;\n"
      "    good = ((v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "            (v1 != v2) && (v1 != v3) && (v2 != v3)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
