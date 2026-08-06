#include "fixture_simulator.h"
#include "helpers_randseq_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 18.17.2: when the if-else condition is false, the production following the
// optional else is generated.
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

// 18.17.2: when the if-else condition is true, the production following the
// expression is generated (and the else production is not).
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

// 18.17.2: the else branch is optional. With no else and a false condition,
// neither the then production nor any else production is generated, so the
// surrounding state is left untouched.
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

// 18.17.2: the else branch is optional, but its absence does not affect the
// then branch. With no else and a true condition, the then production is still
// generated.
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

// 18.17.2: the condition is treated as a Boolean. Any non-zero value is true,
// not just literal 1, so a condition of 5 still selects the then production.
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

// 18.17.2: the condition can be any expression, not just a constant. A
// comparison over a runtime variable drives the branch selection; here n is 3
// so n < 2 is false and the else production is generated.
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

// 18.17.2: the condition may be any expression, including one built from a
// constant form of 11.2.1. Here the condition is a parameter, so resolving it
// takes the parameter-lookup path in expression evaluation rather than reading
// a literal or a procedural variable. With P nonzero the condition is true and
// the then production is generated, pinning the parameter value as the applied
// condition.
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

// 18.17.2: the condition also admits a localparam, a distinct constant form of
// 11.2.1. Here the localparam is zero, so the condition is false and the else
// production is generated. Driving the false branch from a localparam confirms
// the branch follows the constant's value rather than any syntactic default.
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

// 18.17.2: an if-else production statement is one production of a rule, so it
// may sit among other productions in a sequence rather than being the whole
// rule body. Here 'main' generates pre, then the if-else, then post. With the
// condition false the else production (b) is generated in place of the then
// production (a) while the surrounding pre and post productions still generate
// in order: expected total 1 + 100 + 8 = 109, which excludes a's contribution
// of
// 10. This observes the branch selection applying at an embedded position.
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
