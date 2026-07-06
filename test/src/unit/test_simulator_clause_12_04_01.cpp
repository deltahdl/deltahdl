#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalStatementSim, IfElseIfChainSelectsCorrectBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "    else x = 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ConditionalStatementSim, DeepIfElseIfLastElseTaken) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "    else if (0) x = 8'd3;\n"
      "    else x = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(ConditionalStatementSim, IfElseIfFirstConditionTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyFirstMatchTerminatesChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      x = 8'd11;\n"
      "      y = 8'd22;\n"
      "    end else if (1) begin\n"
      "      x = 8'd33;\n"
      "      y = 8'd44;\n"
      "    end else begin\n"
      "      x = 8'd55;\n"
      "      y = 8'd66;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 11u);
  EXPECT_EQ(yv->value.ToUint64(), 22u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyDefaultElseExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0; y = 8'd0;\n"
      "    if (0) begin x = 8'd1; y = 8'd2; end\n"
      "    else if (0) begin x = 8'd3; y = 8'd4; end\n"
      "    else begin x = 8'd55; y = 8'd66; end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 55u);
  EXPECT_EQ(yv->value.ToUint64(), 66u);
}

// §12.4.1: "The expressions shall be evaluated in order. If any expression is
// true, the statement associated with it shall be executed, and this shall
// terminate the whole chain." When an earlier condition is true, a later
// condition carrying a side effect must never be evaluated. The second
// condition here post-increments i; because the first condition is true the
// chain terminates before it, so i stays at its initial value.
TEST(ConditionalStatementSim, IfElseIfFirstTrueSkipsLaterConditionSideEffect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, i;\n"
      "  initial begin\n"
      "    i = 8'd0;\n"
      "    if (1) x = 8'd10;\n"
      "    else if (i++ < 8'd5) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* iv = f.ctx.FindVariable("i");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(iv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 10u);
  EXPECT_EQ(iv->value.ToUint64(),
            0u);  // i++ in the skipped condition never ran
}

// §12.4.1: conditions are evaluated in order until the first true one. The
// first condition here is false but post-increments i as a side effect; the
// second condition then observes the incremented i and is the one that matches.
// x==20 with i==1 proves the earlier condition was evaluated in order before
// the matching one.
TEST(ConditionalStatementSim,
     IfElseIfEarlierConditionSideEffectAppliedInOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, i;\n"
      "  initial begin\n"
      "    i = 8'd0;\n"
      "    if (i++ == 8'd9) x = 8'd10;\n"
      "    else if (i == 8'd1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* iv = f.ctx.FindVariable("i");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(iv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 20u);
  EXPECT_EQ(iv->value.ToUint64(),
            1u);  // first condition's i++ ran, then matched
}

// §12.4.1: the chain's expressions are evaluated in order, and a condition that
// is not a nonzero known value does not match — so the chain proceeds to the
// next condition. Here the first condition is an uninitialized 4-state logic
// (value x), which must not be taken as true; evaluation continues in order to
// the following condition, which matches. x==20 (not 10) shows the x-valued
// condition was skipped and the next one selected in order.
TEST(ConditionalStatementSim, IfElseIfUnknownConditionSkippedContinuesInOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic cond;\n"  // uninitialized 4-state -> x
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    if (cond) x = 8'd10;\n"
      "    else if (1'b1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ConditionalStatementSim, IfElseIfNoMatchNoElseRetainsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd77;\n"
      "    if (0) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
