#include "fixture_real.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates and runs a module with two ints `x` and `y` whose `initial` block
// body is `body`, then returns the resolved `x` and `y` variables (both
// asserted non-null). Used by the prefix/postfix inc/dec return-value tests
// that differ only in the body and expected values.
static void RunXYBody(SimFixture& f, const std::string& body, Variable** vx,
                      Variable** vy) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin " +
          body +
          " end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  *vx = f.ctx.FindVariable("x");
  *vy = f.ctx.FindVariable("y");
  ASSERT_NE(*vx, nullptr);
  ASSERT_NE(*vy, nullptr);
}

TEST(ExpressionSim, PrefixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PrefixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; --x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x++; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PrefixIncReturnsNewValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = ++x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixIncReturnsOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = x++;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 5u);
}

TEST(ExpressionSim, PrefixDecReturnsNewValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 10; y = --x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixDecReturnsOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 10; y = x--;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 9u);
  EXPECT_EQ(vy->value.ToUint64(), 10u);
}

// §11.4.2 states inc/dec behave as blocking assignments. Building the setup
// from the §10.4.1 blocking-assignment `=` and driving it through the full
// pipeline: the standalone `x++` completes before the next statement runs, so
// the later blocking read `y = x` observes the updated value in the same time
// step. A non-blocking (deferred) update would leave y at the pre-increment
// value.
TEST(ExpressionSim, IncrementActsAsBlockingAssignment) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; x++; y = x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

// §11.4.2: the operators need no parentheses in an expression. Here `x++` is an
// operand of a binary `+` with no parentheses; at runtime the postfix form
// contributes the pre-increment value (5) to the sum while x itself advances to
// 6. Observes the no-paren rule producing correct arithmetic, not just an AST
// shape.
TEST(ExpressionSim, PostfixIncrementInBinaryExprUsesOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = x++ + 10;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 15u);
}

// §11.4.2 increment used in a for-loop step, exercised at runtime: each
// iteration applies `i++`, so after the loop i has advanced by 1 per iteration
// (reaching the bound) and the body has run the matching number of times.
TEST(ExpressionSim, IncrementDrivesForLoopIteration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i, count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    for (i = 0; i < 4; i++) count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vi = f.ctx.FindVariable("i");
  auto* vcount = f.ctx.FindVariable("count");
  ASSERT_NE(vi, nullptr);
  ASSERT_NE(vcount, nullptr);
  EXPECT_EQ(vi->value.ToUint64(), 4u);
  EXPECT_EQ(vcount->value.ToUint64(), 4u);
}

// Elaborates and runs a module with two `real` variables `rv` and `res` whose
// `initial` block body is `body`, then reports their final values as doubles.
// The `real` declaration and real-literal initializer are the production
// storage/read path, so inc/dec runs on a genuinely produced real operand
// rather than a hand-assembled one. `res` captures the operator's return value
// so the prefix (new) / postfix (old) distinction is observable alongside the
// §11.4.2 "adjust real operands by 1.0" rule.
static void RunRealBody(SimFixture& f, const std::string& body, double* rv,
                        double* res) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real rv, res;\n"
      "  initial begin " +
          body +
          " end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vrv = f.ctx.FindVariable("rv");
  auto* vres = f.ctx.FindVariable("res");
  ASSERT_NE(vrv, nullptr);
  ASSERT_NE(vres, nullptr);
  *rv = VecToDouble(vrv->value);
  *res = VecToDouble(vres->value);
}

// Prefix ++ on a real adds 1.0 to the operand and yields the incremented value.
TEST(RealIncDecSim, PrefixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = ++rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.5);
  EXPECT_DOUBLE_EQ(res, 3.5);
}

// Prefix -- on a real subtracts 1.0 and yields the decremented value.
TEST(RealIncDecSim, PrefixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = --rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 1.5);
  EXPECT_DOUBLE_EQ(res, 1.5);
}

// Postfix ++ on a real adds 1.0 to the operand but yields the value from before
// the increment.
TEST(RealIncDecSim, PostfixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv++;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 5.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

// Postfix -- on a real subtracts 1.0 but yields the value from before.
TEST(RealIncDecSim, PostfixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv--;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

}  // namespace
