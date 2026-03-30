#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(RelationalEval, LessThanWithXYieldsX) {
  SimFixture f;

  MakeVar4(f, "rl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("rr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "rl"),
                          MakeId(f.arena, "rr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(RelationalEval, GreaterThanWithZYieldsX) {
  SimFixture f;

  MakeVar4(f, "gz", 4, 0b1000, 0b0010);
  auto* b = f.ctx.CreateVariable("g8", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "gz"),
                          MakeId(f.arena, "g8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(RelationalEval, KnownOperandsYieldDefiniteResult) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(RelationalEval, RealComparisonSingleBit) {
  SimFixture f;
  MakeRealVar(f, "rc", 3.14);
  MakeRealVar(f, "rd", 2.71);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "rc"),
                          MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalEval, LessEqualWithXYieldsX) {
  SimFixture f;
  MakeVar4(f, "a", 4, 0b1010, 0b0100);
  auto* b = f.ctx.CreateVariable("b", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(RelationalEval, GreaterEqualWithZYieldsX) {
  SimFixture f;
  MakeVar4(f, "a", 4, 0b1000, 0b0010);
  auto* b = f.ctx.CreateVariable("b", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(RelationalEval, FalseResultIsSingleBit) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(RelationalSignedness, UnsignedUnequalWidthZeroExtends) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 8, 0x10);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalSignedness, SignedUnequalWidthSignExtends) {
  SimFixture f;
  MakeSignedVarAdv(f, "a", 4, 0xE);
  MakeSignedVarAdv(f, "b", 8, 0x05);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalEval, MixedRealIntComparison) {
  SimFixture f;
  MakeRealVar(f, "r", 2.5);
  MakeVar(f, "i", 32, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "r"),
                          MakeId(f.arena, "i"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalEval, RealComparisonFalseResult) {
  SimFixture f;
  MakeRealVar(f, "a", 1.0);
  MakeRealVar(f, "b", 2.0);
  auto* expr = MakeBinary(f.arena, TokenKind::kGtEq, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(OperatorSim, BinaryLessThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 < 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 > 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterOrEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 >= 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryLessOrEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 <= 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, FalseRelationalResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 > 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(RelationalSignedness, SignedNegativeLessThanPositive) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x01);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalSignedness, SignedPositiveGreaterThanNegative) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0x01);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(RelationalSignedness, UnsignedHighValueNotLessThan) {
  SimFixture f;
  auto* a = MakeVar(f, "ua", 8, 0xFF);
  (void)a;
  auto* b = MakeVar(f, "ub", 8, 0x01);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
