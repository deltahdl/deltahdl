#include <gtest/gtest.h>

#include <string>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PrefixDecrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; --x; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

TEST(ExpressionSim, PostfixIncrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x++; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixDecrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; x--; end\n"
      "endmodule\n",
      f, "x");
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

TEST(ExpressionSim, IncrementActsAsBlockingAssignment) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; x++; y = x;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 6u);
}

TEST(ExpressionSim, PostfixIncrementInBinaryExprUsesOldValue) {
  SimFixture f;
  Variable *vx = nullptr, *vy = nullptr;
  RunXYBody(f, "x = 5; y = x++ + 10;", &vx, &vy);
  EXPECT_EQ(vx->value.ToUint64(), 6u);
  EXPECT_EQ(vy->value.ToUint64(), 15u);
}

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

TEST(RealIncDecSim, PrefixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = ++rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.5);
  EXPECT_DOUBLE_EQ(res, 3.5);
}

TEST(RealIncDecSim, PrefixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 2.5; res = --rv;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 1.5);
  EXPECT_DOUBLE_EQ(res, 1.5);
}

TEST(RealIncDecSim, PostfixIncrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv++;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 5.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

TEST(RealIncDecSim, PostfixDecrementBy1Point0) {
  SimFixture f;
  double rv = 0.0, res = 0.0;
  RunRealBody(f, "rv = 4.0; res = rv--;", &rv, &res);
  EXPECT_DOUBLE_EQ(rv, 3.0);
  EXPECT_DOUBLE_EQ(res, 4.0);
}

TEST(ExpressionSim, IncrementWritesAnUnpackedArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin arr[2] = 10; arr[2]++; end\n"
      "endmodule\n",
      f, "arr[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(ExpressionSim, IncrementWritesABitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'h00; d[3]++; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(ExpressionSim, IncrementWritesAPartSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'hF0; d[3:0]++; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF1u);
}

TEST(ExpressionSim, DecrementWritesAStructMember) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin s.hi = 4'd2; s.lo = 4'd5; s.lo--; end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x24u);
}

TEST(ExpressionSim, IncrementEvaluatesItsIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[2] = 10;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()]++;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"arr[2]", 11u}, {"idx_calls", 1u}});
}

static Variable* RunIncDecBody(SimFixture& f, const std::string& decls,
                               const std::string& body, const char* name) {
  return RunAndFindVar("module t;\n  " + decls + "\n  initial begin " + body +
                           " end\nendmodule\n",
                       f, name);
}

TEST(ExpressionSim, IncrementOfAnUnknownYieldsAnUnknown) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "integer i;", "i = 'x; i++;", "i");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval & 0xFFFFFFFFu, 0xFFFFFFFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(ExpressionSim, DecrementOfAnUnknownYieldsAnUnknown) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "integer i;", "i = 'x; i--;", "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(32, 'x'));
}

TEST(ExpressionSim,
     IncrementOfAPartlyUnknownOperandYieldsAnEntirelyUnknownResult) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "logic [7:0] p;", "p = 8'b0000_010x; p++;", "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
}

TEST(ExpressionSim, IncrementAndCompoundAddAgreeOnAnUnknown) {
  SimFixture f;
  auto* vi =
      RunIncDecBody(f, "integer i, j;", "i = 'x; j = 'x; i++; j += 1;", "i");
  ASSERT_NE(vi, nullptr);
  auto* vj = f.ctx.FindVariable("j");
  ASSERT_NE(vj, nullptr);
  EXPECT_FALSE(vi->value.IsKnown());
  EXPECT_EQ(vi->value.ToString(), vj->value.ToString());
}

TEST(ExpressionSim, IncrementOfAWideUnknownIsUnknownAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunIncDecBody(f, "logic [127:0] w;", "w = 'x; w++;", "w");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_NE(var->value.words[1].bval, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(ExpressionSim, PostfixIncrementOfAnUnknownReturnsTheUnknownOldValue) {
  SimFixture f;
  auto* vy = RunIncDecBody(f, "integer x, y;", "x = 'x; y = x++;", "y");
  ASSERT_NE(vy, nullptr);
  auto* vx = f.ctx.FindVariable("x");
  ASSERT_NE(vx, nullptr);
  EXPECT_FALSE(vy->value.IsKnown());
  EXPECT_FALSE(vx->value.IsKnown());
}

}  // namespace
