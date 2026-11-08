#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

void RunNaNbTrial(SimFixture& f, std::string_view main_rule, int iterations,
                  uint64_t& na_count, uint64_t& nb_count) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    for (i = 0; i < " +
      std::to_string(iterations) +
      "; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : " +
      std::string(main_rule) +
      ";\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* na = f.ctx.FindVariable("na");
  auto* nb = f.ctx.FindVariable("nb");
  ASSERT_NE(na, nullptr);
  ASSERT_NE(nb, nullptr);
  na_count = na->value.ToUint64();
  nb_count = nb->value.ToUint64();
}

TEST(RandsequenceSim, ProbabilityProportionalToWeight) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a := 3 | b := 1", 200, na, nb);

  EXPECT_EQ(na + nb, 200u);
  EXPECT_GT(na, 0u);
  EXPECT_GT(nb, 0u);
  EXPECT_GT(na, nb);
}

TEST(RandsequenceSim, ZeroWeightProductionListNeverSelected) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a := 0 | b := 1", 50, na, nb);

  EXPECT_EQ(na, 0u);
  EXPECT_EQ(nb, 50u);
}

TEST(RandsequenceSim, UnspecifiedWeightDefaultsToOne) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a | b := 0", 50, na, nb);

  EXPECT_EQ(na, 50u);
  EXPECT_EQ(nb, 0u);
}

TEST(RandsequenceSim, WeightEvaluatedDynamicallyFromExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic g;\n"
      "  logic [7:0] x1, x2;\n"
      "  initial begin\n"
      "    g = 1'b1;\n"
      "    randsequence(m1)\n"
      "      m1 : p := g | q := (1'b1 - g);\n"
      "      p : { x1 = 8'd1; };\n"
      "      q : { x1 = 8'd2; };\n"
      "    endsequence\n"
      "    g = 1'b0;\n"
      "    randsequence(m2)\n"
      "      m2 : r := g | s := (1'b1 - g);\n"
      "      r : { x2 = 8'd1; };\n"
      "      s : { x2 = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x1 = f.ctx.FindVariable("x1");
  auto* x2 = f.ctx.FindVariable("x2");
  ASSERT_NE(x1, nullptr);
  ASSERT_NE(x2, nullptr);

  EXPECT_EQ(x1->value.ToUint64(), 1u);
  EXPECT_EQ(x2->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, DefaultWeightOfOneRelativeToExplicit) {
  SimFixture f;
  uint64_t na = 0, nb = 0;
  RunNaNbTrial(f, "a | b := 3", 200, na, nb);

  EXPECT_EQ(na + nb, 200u);
  EXPECT_GT(na, 0u);
  EXPECT_GT(nb, 0u);
  EXPECT_GT(nb, 2u * na);
}

TEST(RandsequenceSim, WeightOnNonAlternativeProductionIsIgnored) {
  SimFixture f;
  auto* na = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] na;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0;\n"
      "    for (i = 0; i < 50; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : a := 0;\n"
      "        a : { na = na + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "na");
  ASSERT_NE(na, nullptr);

  EXPECT_EQ(na->value.ToUint64(), 50u);
}

TEST(RandsequenceSim, ParameterWeightSelectsProductionList) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  parameter WA = 1;\n"
      "  parameter WB = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := WA | b := WB;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, LocalparamWeightSelectsProductionList) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  localparam LA = 0;\n"
      "  localparam LB = 1;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := LA | b := LB;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, WeightExpressionEvaluatedOncePerSelection) {
  SimFixture f;
  auto* cnt = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] cnt;\n"
      "  logic [7:0] x;\n"
      "  function int bump();\n"
      "    cnt = cnt + 1;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    cnt = 0;\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := (bump()) | b := (bump()) | c := (bump());\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "      c : { x = 8'd3; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(cnt, nullptr);
  EXPECT_EQ(cnt->value.ToUint64(), 3u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_GE(x->value.ToUint64(), 1u);
  EXPECT_LE(x->value.ToUint64(), 3u);
}

TEST(RandsequenceSim, WeightReadingItsOwnIncrementSelectsFromTheSummedWeights) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int unsigned w;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    w = 0;\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : a := (w++) | b := 1;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 2u);
}

void RunWeightOnce(SimFixture& f, std::string_view main_rule) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb;\n"
      "  initial begin\n"
      "    na = 0; nb = 0;\n"
      "    randsequence(main)\n"
      "      main : " +
      std::string(main_rule) +
      ";\n"
      "      a : { na = na + 1; };\n"
      "      b : { nb = nb + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

TEST(RandsequenceSim, NegativeWeightIsReported) {
  SimFixture f;
  RunWeightOnce(f, "a := (-1) | b := 1");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a weight needs a known integral value of zero or "
                            "more",
                            6, "18.17.1"));
}

TEST(RandsequenceSim, UnknownWeightIsReported) {
  SimFixture f;
  RunWeightOnce(f, "a := 1'bx | b := 1");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a weight needs a known integral value of zero or "
                            "more",
                            6, "18.17.1"));
}

void RunAbcTrial(SimFixtureSeeded& f, std::string_view main_rule,
                 int iterations, std::vector<uint64_t>& counts) {
  std::string src =
      "module t;\n"
      "  logic [31:0] na, nb, nc;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    na = 0; nb = 0; nc = 0;\n"
      "    for (i = 0; i < " +
      std::to_string(iterations) +
      "; i = i + 1)\n"
      "      randsequence(main)\n"
      "        main : " +
      std::string(main_rule) +
      ";\n"
      "        a : { na = na + 1; };\n"
      "        b : { nb = nb + 1; };\n"
      "        c : { nc = nc + 1; };\n"
      "      endsequence\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (const char* name : {"na", "nb", "nc"}) {
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr);
    counts.push_back(var->value.ToUint64());
  }
}

TEST(RandsequenceSim, WeightsSummingPastThirtyTwoBitsReachEveryRule) {
  SimFixtureSeeded f;
  std::vector<uint64_t> counts;
  RunAbcTrial(f, "a := 64'h1_0000_0000 | b := 64'h1_0000_0000", 40, counts);
  EXPECT_GT(counts[0], 0u);
  EXPECT_GT(counts[1], 0u);
}

TEST(RandsequenceSim, AThirdRuleBeyondTwoBlocksIsStillReachable) {
  SimFixtureSeeded f;
  std::vector<uint64_t> counts;
  RunAbcTrial(
      f, "a := 64'h1_0000_0000 | b := 64'h1_0000_0000 | c := 64'h1_0000_0000",
      60, counts);
  EXPECT_GT(counts[0], 0u);
  EXPECT_GT(counts[2], 0u);
}

}  // namespace
