#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/constraint_solver.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, RandsequenceBasicProduction) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "production";
  v.min_val = 0;
  v.max_val = 2;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_seq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "production";
  c.dist_weights = {{0, 1}, {1, 1}, {2, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("production");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 2);
}

TEST(RandsequenceSim, CodeBlockSideEffect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : { x = 8'd42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(RandsequenceSim, ProductionSequenceOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { x = x + 8'd10; };\n"
      "      second : { x = x + 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(RandsequenceSim, NamedTopProductionDesignatesEntry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(second)\n"
      "      first  : { x = 8'd11; };\n"
      "      second : { x = 8'd99; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(RandsequenceSim, AlternativeProductionListsChosenAtRandom) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer ca;\n"
      "  integer cb;\n"
      "  initial begin\n"
      "    ca = 0;\n"
      "    cb = 0;\n"
      "    for (int i = 0; i < 200; i++) begin\n"
      "      randsequence(main)\n"
      "        main : a | b;\n"
      "        a : { ca = ca + 1; };\n"
      "        b : { cb = cb + 1; };\n"
      "      endsequence\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* ca = f.ctx.FindVariable("ca");
  auto* cb = f.ctx.FindVariable("cb");
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(cb, nullptr);
  EXPECT_GT(ca->value.ToUint64(), 0u);
  EXPECT_GT(cb->value.ToUint64(), 0u);
  EXPECT_EQ(ca->value.ToUint64() + cb->value.ToUint64(), 200u);
}

TEST(RandsequenceSim, NoProductionNameUsesFirst) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence()\n"
      "      top : { x = 8'd55; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(RandsequenceSim, NonterminalDecomposesToTerminals) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main  : group tail;\n"
      "      group : alpha beta;\n"
      "      alpha : { x = x * 10 + 1; };\n"
      "      beta  : { x = x * 10 + 2; };\n"
      "      tail  : { x = x * 10 + 3; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(RandsequenceSim, ChosenProductionListStreamsItemsInOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : p q | r s;\n"
      "      p : { x = x * 10 + 1; };\n"
      "      q : { x = x * 10 + 2; };\n"
      "      r : { x = x * 10 + 3; };\n"
      "      s : { x = x * 10 + 4; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  auto result = var->value.ToUint64();
  EXPECT_TRUE(result == 12u || result == 34u);
}

TEST(RandsequenceSim, SequencedCodeBlockTerminalsRunInOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : { x = x * 10 + 1; } { x = x * 10 + 2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(RandsequenceSim, ProductionIdentifiersAreLocalToRandsequenceScope) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer log;\n"
      "  initial begin\n"
      "    log = 0;\n"
      "    randsequence(main)\n"
      "      main : { log = log * 10 + 1; };\n"
      "    endsequence\n"
      "    randsequence(main)\n"
      "      main : { log = log * 10 + 2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "log");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(RandsequenceSim, CodeBlockLocalsAreAutomaticPerInvocation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : p p;\n"
      "      p : { int y; y = y + 1; acc = acc + y; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, WeightCodeBlockLocalsAreAutomaticPerActivation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : a a;\n"
      "      a : p := 1 { int y; y = y + 1; acc = acc + y; };\n"
      "      p : { acc = acc + 10; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(RandsequenceSim, RandJoinOperandWeightCodeBlockLocalsAreAutomatic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : m m;\n"
      "      m : rand join p q;\n"
      "      p : s := 1 { int y; y = y + 1; acc = acc + y; };\n"
      "      q : s;\n"
      "      s : { acc = acc + 10; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
