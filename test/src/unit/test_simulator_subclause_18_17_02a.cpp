#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_randseq_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, IfElseProductionFalseSelectsElse) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (0) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, IfElseProductionTrueSelectsThen) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (1) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, IfWithoutElseFalseGeneratesNothing) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd5;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (0) a;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(RandsequenceSim, IfWithoutElseTrueGeneratesThen) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd5;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (1) a;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, NonOneTruthyConditionSelectsThen) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (5) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, ConditionFromExpressionSelectsBranch) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  logic [7:0] n;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    n = 8'd3;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (n < 2) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, ParameterConditionSelectsThen) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  parameter P = 1;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (P) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, LocalparamConditionSelectsElse) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  localparam L = 0;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (L) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RandsequenceSim, IfElseEmbeddedInProductionSequenceSelectsElse) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : pre if (0) a else b post;\n"
                                   "      pre  : { x = x + 8'd1; };\n"
                                   "      a    : { x = x + 8'd10; };\n"
                                   "      b    : { x = x + 8'd100; };\n"
                                   "      post : { x = x + 8'd8; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 109u);
}

}  // namespace
