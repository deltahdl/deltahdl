#include "builders_ast.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TernaryOperatorSim, TernaryMultipleInExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = (a ? 10 : 20) + (b ? 30 : 40);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(TernaryOperatorSim, TernaryResultInComputation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result = (sel ? 6 : 3) * 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryOperatorSim, TernaryBitSelectCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] flags;\n"
      "  int result;\n"
      "  initial begin\n"
      "    flags = 8'b0000_0100;\n"
      "    result = flags[2] ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(TernaryOperatorSim, TernaryPartSelectOperands) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    result = 1 ? data[15:8] : data[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(TernaryOperatorSim, TernaryResultWidth8Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h01;\n"
      "    result = 1 ? a : b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(TernaryOperatorSim, TernaryResultWidth32Bit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 1 ? 32'hDEAD_BEEF : 32'h0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(TernaryOperatorSim, TernaryNestedOuterFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0 ? (1 ? 10 : 20) : 30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(TernaryOperatorSim, TernaryChainedDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sel, result;\n"
      "  initial begin\n"
      "    sel = 5;\n"
      "    result = (sel == 0) ? 100 :\n"
      "             (sel == 1) ? 200 :\n"
      "             (sel == 2) ? 300 : 999;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 999u);
}

TEST(TernaryOperatorSim, TernaryLogicalAndCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 4;\n"
      "    result = (a && b) ? 55 : 66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(ConditionalAmbiguousCondition, BothBranchSideEffectsExecute) {
  SimFixture f;
  MakeVar4(f, "cond", 1, 0, 1);
  MakeVar(f, "se_t", 8, 99);
  MakeVar(f, "se_f", 8, 99);
  EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "cond"),
                       MakeAssignExpr(f.arena, "se_t", 11),
                       MakeAssignExpr(f.arena, "se_f", 22)),
           f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("se_t")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("se_f")->value.ToUint64(), 22u);
}

TEST(ConditionalAmbiguousCondition, AllZeroBranchesCombineToZero) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b0000);
  MakeVar(f, "e", 4, 0b0000);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(ConditionalAmbiguousCondition, AllOneBranchesCombineToOne) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b1111);
  MakeVar(f, "e", 4, 0b1111);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0b1111u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(ConditionalAmbiguousCondition, AllDifferingBitsBecomeX) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "t", 4, 0b1010);
  MakeVar(f, "e", 4, 0b0101);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval & ~result.words[0].bval, 0u);
  EXPECT_EQ(result.words[0].bval, 0b1111u);
}

TEST(ConditionalAmbiguousCondition, XInBranchesPropagates) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  auto* tv = f.ctx.CreateVariable("t", 4);
  tv->value = MakeLogic4Vec(f.arena, 4);
  tv->value.words[0].aval = 0b1111;
  tv->value.words[0].bval = 0b0010;
  MakeVar(f, "e", 4, 0b1111);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);

  EXPECT_NE(result.words[0].bval & 0b0010u, 0u);
}

TEST(ConditionalAmbiguousCondition, DifferentWidthBranchesCombinedToMaxWidth) {
  SimFixture f;
  MakeVar4(f, "xc", 1, 0, 1);
  MakeVar(f, "narrow", 4, 0b1111);
  MakeVar(f, "wide", 8, 0b11110000);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "xc"),
                           MakeId(f.arena, "narrow"), MakeId(f.arena, "wide")),
               f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

TEST(ConditionalAmbiguousCondition, MultiBitPartialXTriggersAmbiguous) {
  SimFixture f;
  auto* cv = f.ctx.CreateVariable("cond", 4);
  cv->value = MakeLogic4Vec(f.arena, 4);
  cv->value.words[0].aval = 0b0001;
  cv->value.words[0].bval = 0b0010;
  MakeVar(f, "t", 4, 0b1100);
  MakeVar(f, "e", 4, 0b1010);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "cond"),
                           MakeId(f.arena, "t"), MakeId(f.arena, "e")),
               f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval, 0b1110u);  // differing bits -> x = (1, 1)
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

TEST(TernaryOperatorSim, CondPredicateTripleAndBothTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 1;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(TernaryOperatorSim, CondPredicateTripleAndFirstFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TernaryOperatorSim, CondPredicateTripleAndSecondFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 0;\n"
      "    result = (a &&& b) ? 42 : 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §11.4.11: when one branch is real and the other integral, the integral branch
// is cast to real and the result type is real. The selected integral operand
// must contribute its numeric value, not its raw bit pattern.
TEST(ConditionalRealResult, IntegralSelectedBranchCastToReal) {
  // Condition true selects the integral branch; the real second branch still
  // forces a real result, so 5 must be delivered as 5.0.
  double v = RunAndGetReal(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1 ? 5 : 2.5;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 5.0);
}

TEST(ConditionalRealResult, IntegralUnselectedBranchStillForcesReal) {
  // Condition false selects the integral second branch; the real first branch
  // forces a real result, so the integer 7 must be delivered as 7.0.
  double v = RunAndGetReal(
      "module t;\n"
      "  real r;\n"
      "  initial r = 0 ? 2.5 : 7;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 7.0);
}

TEST(ConditionalRealResult, SignedIntegralBranchCastPreservesSign) {
  // A signed integral branch cast to real keeps its negative value rather than
  // reinterpreting the two's-complement pattern as a large positive number.
  double v = RunAndGetReal(
      "module t;\n"
      "  int i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = -3;\n"
      "    r = 1 ? i : 2.5;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, -3.0);
}

TEST(ConditionalRealResult, BothBranchesRealUnchanged) {
  // Regression guard for the real early-return path: a plain both-real
  // conditional still selects the taken real branch verbatim.
  double v = RunAndGetReal(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1 ? 2.5 : 3.5;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 2.5);
}

// §11.4.11: when the condition is ambiguous (x/z) and both branches are
// logically equivalent, the operator returns that shared value. Driven from
// real source syntax (a 1'bx-valued logic condition) through the full pipeline
// so the ambiguous-condition path is reached the way a design would reach it,
// not by hand-constructing a 4-state operand.
TEST(ConditionalAmbiguousCondition,
     XConditionEqualBranchesReturnsValueEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic c;\n"
                      "  logic [3:0] a, b, r;\n"
                      "  initial begin\n"
                      "    c = 1'bx;\n"
                      "    a = 4'hA;\n"
                      "    b = 4'hA;\n"
                      "    r = c ? a : b;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xAu);
}

// §11.4.11: an ambiguous condition with integral, non-equivalent branches
// combines the two results bit by bit (Table 11-20) — each bit that agrees is
// kept, each bit that differs becomes x. Full pipeline from a 1'bx condition:
// a and b agree on bits 3/1/0 and differ on bit 2.
TEST(ConditionalAmbiguousCondition, XConditionDiffersCombinesBitwiseEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic c;\n"
      "  logic [3:0] a, b, r;\n"
      "  logic bit3, bit1;\n"
      "  integer unk;\n"
      "  initial begin\n"
      "    c = 1'bx;\n"
      "    a = 4'b1100;\n"
      "    b = 4'b1000;\n"
      "    r = c ? a : b;\n"
      "    unk = $isunknown(r);\n"
      "    bit3 = r[3];\n"
      "    bit1 = r[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  // Differing bit 2 forces the result unknown; the agreeing bits survive.
  LowerRunAndCheck(f, design, {{"unk", 1u}, {"bit3", 1u}, {"bit1", 0u}});
}

// §11.4.11: a z-valued condition is ambiguous exactly as an x-valued one is
// (both are unknown). With logically-equivalent branches the shared value is
// returned. This is the z counterpart to the x end-to-end test above, driven
// from a 1'bz literal through the full pipeline.
TEST(ConditionalAmbiguousCondition,
     ZConditionEqualBranchesReturnsValueEndToEnd) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic c;\n"
                      "  logic [3:0] a, b, r;\n"
                      "  initial begin\n"
                      "    c = 1'bz;\n"
                      "    a = 4'hA;\n"
                      "    b = 4'hA;\n"
                      "    r = c ? a : b;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            0xAu);
}

// §11.4.11: besides integral operands, the conditional operator also applies to
// aggregate operands. With a determinate condition a packed-struct branch is
// selected whole; reading the selected struct back confirms its bits flowed
// through. Built from a real packed-struct declaration and struct literals.
TEST(TernaryOperatorSim, PackedStructAggregateBranchSelected) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } "
                "pair_t;\n"
                "  pair_t s1, s2, r;\n"
                "  initial begin\n"
                "    s1 = '{4'hA, 4'h5};\n"
                "    s2 = '{4'h3, 4'hC};\n"
                "    r = 1 ? s1 : s2;\n"
                "  end\n"
                "endmodule\n",
                "r"),
      0xA5u);
}

// §11.4.11: with an ambiguous condition and a real (nonintegral) result, the
// branches are compared for numeric equivalence. When they differ, the result
// is the default value for the type (Table 7-1: 0.0 for real) rather than a
// bit-by-bit combination of the two operands' bit patterns.
TEST(ConditionalRealResult, AmbiguousRealBranchesNotEquivalentReturnDefault) {
  double v = RunAndGetReal(
      "module t;\n"
      "  logic c;\n"
      "  real r;\n"
      "  initial begin\n"
      "    c = 1'bx;\n"
      "    r = c ? 2.5 : 3.5;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 0.0);
}

// §11.4.11: an ambiguous condition with numerically-equivalent real branches
// returns that shared value.
TEST(ConditionalRealResult, AmbiguousRealBranchesEquivalentReturnValue) {
  double v = RunAndGetReal(
      "module t;\n"
      "  logic c;\n"
      "  real r;\n"
      "  initial begin\n"
      "    c = 1'bx;\n"
      "    r = c ? 4.5 : 4.5;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 4.5);
}

}  // namespace
