#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, CaseProduction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (1) 0: a; 1: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(RandsequenceSim, CaseProductionEvaluatesExpressions) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] sel;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    sel = 8'd6;\n"
      "    randsequence(main)\n"
      "      main : case (sel & 8'd3) 1+0: a; 1+1: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(RandsequenceSim, CaseProductionCommaSharedExpressions) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (2) 0, 1, 2: a; default: b; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(RandsequenceSim, CaseProductionDefaultWhenNoMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (7) 0: a; 1: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(RandsequenceSim, CaseProductionDefaultIsFallbackRegardlessOfPosition) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (1) default: c; 1: b; endcase;\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(RandsequenceSim, CaseProductionFirstMatchingItemWinsWhenSeveralMatch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (5) 5: a; 5: b; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(RandsequenceSim, CaseProductionParameterCaseExpressionSelectsProduction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = 2;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (P) 1: a; 2: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(RandsequenceSim, CaseProductionLocalparamCaseItemSelectsProduction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam L = 3;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (3) L: a; default: b; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(RandsequenceSim, CaseProductionNoMatchNoDefaultGeneratesNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd99;\n"
      "    randsequence(main)\n"
      "      main : case (7) 0: a; 1: b; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
