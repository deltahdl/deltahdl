#include <gtest/gtest.h>

#include <cstdint>

#include "builders_ast.h"
#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SignedUnsignedArithmetic, SignedDivisionTruncatesTowardZero) {
  SimFixture f;
  MakeSignedVarAdv(f, "sd", 8, 0xF9);
  MakeSignedVarAdv(f, "se", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "se"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFDu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, SignedModulusSignFollowsFirstOperand) {
  SimFixture f;
  MakeSignedVarAdv(f, "sm", 8, 0xF9);
  MakeSignedVarAdv(f, "sn", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm"),
                          MakeId(f.arena, "sn"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, SignedMultiplyNegativeOperand) {
  SimFixture f;
  MakeSignedVarAdv(f, "ma", 8, 0xFD);
  MakeSignedVarAdv(f, "mb", 8, 4);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "ma"),
                          MakeId(f.arena, "mb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xF4u);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, SignedModulusNegativeDivisor) {
  SimFixture f;

  MakeSignedVarAdv(f, "sm2", 8, 11);
  MakeSignedVarAdv(f, "sn2", 8, 0xFD);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm2"),
                          MakeId(f.arena, "sn2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFF, 2u);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, UnsignedDivisionTruncates) {
  SimFixture f;
  auto* a = MakeVar(f, "ud", 8, 0xF9);
  (void)a;
  auto* b = MakeVar(f, "ue", 8, 2);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "ud"),
                          MakeId(f.arena, "ue"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 124u);
}

TEST(SignedUnsignedArithmetic, PowerNegativeExponentReturnsZero) {
  SimFixture f;

  MakeSignedVarAdv(f, "pb", 8, 3);

  MakeSignedVarAdv(f, "pe", 8, 0xFE);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "pb");
  expr->rhs = MakeId(f.arena, "pe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SignedUnsignedArithmetic, PowerZeroBaseNegativeExponentReturnsX) {
  SimFixture f;

  MakeSignedVarAdv(f, "zb", 8, 0);
  MakeSignedVarAdv(f, "ze", 8, 0xFF);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "zb");
  expr->rhs = MakeId(f.arena, "ze");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SignedUnsignedArithmetic, PowerNegativeOneOddExponentReturnsNegativeOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1", 8, 0xFF);
  MakeSignedVarAdv(f, "n3", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n3");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, PowerNegativeOneEvenExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1", 8, 0xFF);
  MakeSignedVarAdv(f, "n4", 8, 4);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n4");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, PowerNegativeBasePositiveExponent) {
  SimFixture f;

  MakeSignedVarAdv(f, "nb", 8, 0xFD);
  MakeSignedVarAdv(f, "ne", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "nb");
  expr->rhs = MakeId(f.arena, "ne");
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFF, 0xE5u);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, PowerNegativeBaseNegativeExponentReturnsZero) {
  SimFixture f;

  MakeSignedVarAdv(f, "nb2", 8, 0xFD);
  MakeSignedVarAdv(f, "ne2", 8, 0xFF);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "nb2");
  expr->rhs = MakeId(f.arena, "ne2");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SignedUnsignedArithmetic, PowerOneBaseNegativeExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "ob", 8, 1);
  MakeSignedVarAdv(f, "oe", 8, 0xFE);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "ob");
  expr->rhs = MakeId(f.arena, "oe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(SignedUnsignedArithmetic,
     PowerNegativeOneNegativeOddExponentReturnsNegativeOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1a", 8, 0xFF);
  MakeSignedVarAdv(f, "n3a", 8, 0xFD);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1a");
  expr->rhs = MakeId(f.arena, "n3a");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, PowerNegativeOneNegativeEvenExponentReturnsOne) {
  SimFixture f;

  MakeSignedVarAdv(f, "n1b", 8, 0xFF);
  MakeSignedVarAdv(f, "n4b", 8, 0xFC);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1b");
  expr->rhs = MakeId(f.arena, "n4b");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, SignedAdditionProducesSignedResult) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFE);
  MakeSignedVarAdv(f, "sb", 8, 0xFD);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFBu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, SignedSubtractionProducesSignedResult) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 3);
  MakeSignedVarAdv(f, "sb", 8, 5);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFEu);
  EXPECT_TRUE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, MixedSignednessProducesUnsignedResult) {
  SimFixture f;
  MakeSignedVarAdv(f, "sv", 8, 0xFE);
  MakeVar(f, "uv", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sv"),
                          MakeId(f.arena, "uv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_FALSE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, UnsignedAdditionProducesUnsignedResult) {
  SimFixture f;
  MakeVar(f, "ua", 8, 200);
  MakeVar(f, "ub", 8, 100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0x2Cu);
  EXPECT_FALSE(result.is_signed);
}

TEST(SignedUnsignedArithmetic, EndToEndSignedDivision) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a, b, r;\n"
      "  initial begin\n"
      "    a = -12;\n"
      "    b = 3;\n"
      "    r = a / b;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(),
            static_cast<uint64_t>(static_cast<uint32_t>(-4)));
  EXPECT_TRUE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, EndToEndSignedModulus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a, b, r;\n"
      "  initial begin\n"
      "    a = -10;\n"
      "    b = 3;\n"
      "    r = a % b;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(),
            static_cast<uint64_t>(static_cast<uint32_t>(-1)));
}

TEST(SignedUnsignedArithmetic, EndToEndUnsignedHighBitInterpretation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, r;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    r = a / 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 120u);
}

TEST(SignedUnsignedArithmetic, SignedVarIdentifierPreservesSignedness) {
  SimFixture f;
  MakeSignedVarAdv(f, "sv", 8, 0xFF);
  auto result = EvalExpr(MakeId(f.arena, "sv"), f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
}

TEST(SignedUnsignedArithmetic, UnsignedVarIdentifierPreservesUnsigned) {
  SimFixture f;
  MakeVar(f, "uv", 8, 0xFF);
  auto result = EvalExpr(MakeId(f.arena, "uv"), f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
}

TEST(SignedUnsignedArithmetic, SignedNetPropagatesSignednessToSimVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire signed [7:0] w;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);
}

TEST(SignedUnsignedArithmetic,
     SameBitPatternDifferentInterpretationSignedVsUnsigned) {
  SimFixture f;

  MakeSignedVarAdv(f, "sv", 8, 0xF9);
  MakeVar(f, "uv", 8, 0xF9);

  auto* sdiv = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "sv"),
                          MakeId(f.arena, "sv"));
  auto sresult = EvalExpr(sdiv, f.ctx, f.arena);

  EXPECT_EQ(sresult.ToUint64(), 1u);
  EXPECT_TRUE(sresult.is_signed);

  auto* udiv = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "uv"),
                          MakeId(f.arena, "uv"));
  auto uresult = EvalExpr(udiv, f.ctx, f.arena);

  EXPECT_EQ(uresult.ToUint64(), 1u);
  EXPECT_FALSE(uresult.is_signed);
}

TEST(SignedUnsignedArithmetic, RealArithmeticPreservesNegativeFraction) {
  SimFixture f;
  MakeRealVar(f, "rc", 2.0);
  MakeRealVar(f, "rd", 7.5);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "rc"),
                          MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), -5.5);
}

TEST(SignedUnsignedArithmetic, EndToEndSignedToUnsignedConversionKeepsBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int s;\n"
      "  int unsigned u;\n"
      "  initial begin\n"
      "    s = -1;\n"
      "    u = s;\n"
      "  end\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(),
            static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_FALSE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, EndToEndUnsignedToSignedConversionKeepsBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] u;\n"
      "  int s;\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFF;\n"
      "    s = u;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(),
            static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  EXPECT_TRUE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, SignedDivisionQuotientIntoUnsignedTargetWraps) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int intS;\n"
      "  logic [15:0] u;\n"
      "  initial begin\n"
      "    intS = -12;\n"
      "    u = intS / 3;\n"
      "  end\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFFFu, 65532u);
  EXPECT_FALSE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, UnsignedVariableDivisionEvaluatedUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] u;\n"
      "  int intS;\n"
      "  initial begin\n"
      "    u = 16'hFFF4;\n"
      "    intS = u / 3;\n"
      "  end\n"
      "endmodule\n",
      f, "intS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFFFFFFFu, 21841u);
  EXPECT_TRUE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, RealDivisionKeepsFractionEndToEnd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real a, b, r;\n"
      "  initial begin\n"
      "    a = 15.0;\n"
      "    b = 2.0;\n"
      "    r = a / b;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(VecToDouble(var->value), 7.5);
}

TEST(SignedUnsignedArithmetic, SignedNetOperandUsesSignedArithmetic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire signed [7:0] a;\n"
      "  logic signed [7:0] q;\n"
      "  assign a = -8'sd12;\n"
      "  initial begin\n"
      "    #1;\n"
      "    q = a / 8'sd3;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xFCu);
  EXPECT_TRUE(var->is_signed);
}

TEST(SignedUnsignedArithmetic, UnsignedNetOperandUsesUnsignedArithmetic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  logic [7:0] q;\n"
      "  assign a = 8'hF0;\n"
      "  initial begin\n"
      "    #1;\n"
      "    q = a / 8'sd2;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 120u);
  EXPECT_FALSE(var->is_signed);
}

}  // namespace
