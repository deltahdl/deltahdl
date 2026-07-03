#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(EvalSteps, ShiftAmountSelfDetermined) {
  SimFixture f;
  MakeVar(f, "v", 8, 0x01);
  MakeVar(f, "sh", 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sh"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x08u);
  EXPECT_EQ(result.width, 8u);
}

TEST(EvalSteps, RelationalOperandsMutuallyDetermined) {
  SimFixture f;
  MakeVar(f, "r4", 4, 0xF);
  MakeVar(f, "r8", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "r4"),
                          MakeId(f.arena, "r8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalSteps, TernaryCondSelfDetermined) {
  SimFixture f;
  MakeVar(f, "cond", 8, 0xFF);
  MakeVar(f, "tv", 8, 42);
  MakeVar(f, "fv", 4, 0);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "cond");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(EvalSteps, WidthPropFromContext) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("wa", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xF);
  auto* vb = f.ctx.CreateVariable("wb", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "wa"),
                          MakeId(f.arena, "wb"));

  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
  EXPECT_EQ(r2.width, 8u);
}

TEST(EvalSteps, AssignmentContextWidthPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(EvalSteps, ContextWidthPropagatesForMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a * a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xE1u);
}

TEST(EvalSteps, SubtractionContextWidthPreservesBorrow) {
  SimFixture f;

  MakeVar(f, "sa", 8, 0);
  MakeVar(f, "sb", 8, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));

  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0xFFu);
  EXPECT_EQ(r1.width, 8u);

  auto r2 = EvalExpr(expr, f.ctx, f.arena, 16);
  EXPECT_EQ(r2.ToUint64(), 0xFFFFu);
  EXPECT_EQ(r2.width, 16u);
}

TEST(EvalSteps, DivisionContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a / 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(EvalSteps, ModulusContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a % 4'hB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(EvalSteps, BitwiseAndContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 4'hA;\n"
      "    result = a & b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(EvalSteps, BitwiseOrContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    b = 4'hA;\n"
      "    result = a | b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(EvalSteps, BitwiseXorContextWidthFromLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 4'h3;\n"
      "    result = a ^ b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(EvalSteps, ComparisonResultWidthIgnoresContext) {
  SimFixture f;
  MakeVar(f, "ca", 8, 5);
  MakeVar(f, "cb", 8, 10);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ca"),
                          MakeId(f.arena, "cb"));
  auto result = EvalExpr(expr, f.ctx, f.arena, 16);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalSteps, EqualityResultWidthIgnoresContext) {
  SimFixture f;
  MakeVar(f, "ea", 8, 7);
  MakeVar(f, "eb", 8, 7);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "ea"),
                          MakeId(f.arena, "eb"));
  auto result = EvalExpr(expr, f.ctx, f.arena, 16);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalSteps, SignedComparisonResultZeroExtendedNotSignExtended) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a, b;\n"
      "  logic signed [7:0] result;\n"
      "  initial begin\n"
      "    a = -4'sd1;\n"
      "    b = 4'sd0;\n"
      "    result = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01u);
}

TEST(EvalSteps, SignedRelationalOperandsSignExtendToSharedWidth) {
  // §11.8.2: a relational operator's operands mutually determine a shared
  // width (the larger of the two) and each is sign-extended when its declared
  // type is signed, independent of the surrounding context. The 4-bit -1 must
  // sign-extend to stay negative rather than reading as 15 in the comparison.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = -4'sd1;\n"
      "    b = 8'sd5;\n"
      "    result = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // -1 < 5 is true; a zero-extended operand would compare 15 < 5 (false).
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalSteps, SignedEqualityOperandsSignExtendToSharedWidth) {
  // §11.8.2: an equality operator's operands mutually determine the larger
  // width and sign-extend when signed. The narrow -1 must sign-extend to the
  // wider -1 to compare equal.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = -4'sd1;\n"
      "    b = -8'sd1;\n"
      "    result = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Both are -1; a zero-extended narrow operand (0x0F) would differ from 0xFF.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalSteps, TernaryBranchesReceiveContextWidth) {
  SimFixture f;
  MakeVar(f, "tc", 1, 1);
  MakeVar(f, "ta", 4, 0xF);
  MakeVar(f, "tb", 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "ta");
  tern->false_expr = MakeId(f.arena, "tb");
  auto result = EvalExpr(tern, f.ctx, f.arena, 8);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
}

TEST(EvalSteps, SignedOperandSignExtendsInWiderContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] result;\n"
      "  initial begin\n"
      "    s = -4'sd1;\n"
      "    result = s + s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFEu);
}

TEST(EvalSteps, MixedSignedAndUnsignedOperandUsesUnsignedExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    s = -4'sd1;\n"
      "    u = 4'd1;\n"
      "    result = s + u;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x10u);
}

TEST(EvalSteps, IntegerContextOperandConvertedToRealForRealResultOperator) {
  // §11.8.2 exception 1: when an operator's result type is real, a
  // context-determined operand that is not real is treated as self-determined
  // and converted to real just before the operator is applied. Here the int
  // operand of `+` is promoted to real, driven from real source declarations
  // through the full pipeline.
  double result = RunAndGetReal(
      "module t;\n"
      "  int i;\n"
      "  real r;\n"
      "  real result;\n"
      "  initial begin\n"
      "    i = 255;\n"
      "    r = 0.5;\n"
      "    result = i + r;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // Integer addition would drop the fractional part; 255.5 confirms i became
  // real before the operator was applied.
  EXPECT_DOUBLE_EQ(result, 255.5);
}

TEST(EvalSteps, RelationalWithRealOperandComparesInRealAndYieldsOneBit) {
  // §11.8.2 exception 2: relational operands affect each other, so a real
  // operand pulls its integer partner into a real comparison, while the result
  // is a 1-bit unsigned value. Built from real/int declarations end-to-end.
  uint64_t result = RunAndGet(
      "module t;\n"
      "  real r;\n"
      "  int i;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    r = 3.5;\n"
      "    i = 3;\n"
      "    result = (r > i);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // 3.5 > 3 is true; a truncated integer comparison (3 > 3) would be false.
  EXPECT_EQ(result, 1u);
}

TEST(EvalSteps, UnsignedOperandZeroExtendsInWiderContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u = 4'hF;\n"
      "    result = u + u;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1Eu);
}

TEST(EvalSteps, SignedParameterOperandSignExtendsInWiderContext) {
  // §11.8.2: when propagation reaches a simple operand (11.5) it is converted
  // to the propagated width and sign-extended only when signed. Here the simple
  // operand is a signed parameter rather than a variable or literal, built from
  // real parameter syntax and evaluated end-to-end.
  uint64_t r = RunAndGet(
      "module t;\n"
      "  parameter signed [3:0] P = -4'sd1;\n"
      "  logic signed [7:0] r;\n"
      "  initial r = P + P;\n"
      "endmodule\n",
      "r");
  // -1 + -1 = -2 -> 0xFE; treating P as unsigned would give 15 + 15 = 0x1E.
  EXPECT_EQ(r, 0xFEu);
}

TEST(EvalSteps, RealEqualityOperandPullsIntegerPartnerIntoRealCompare) {
  // §11.8.2 exception 2: an equality operand that is real makes the comparison
  // happen in the real domain (the integer partner is converted), while the
  // result stays a 1-bit unsigned value. This exercises the equality path,
  // distinct from the relational path, built from real/int declarations.
  uint64_t result = RunAndGet(
      "module t;\n"
      "  real r;\n"
      "  int i;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    r = 2.5;\n"
      "    i = 2;\n"
      "    result = (r != i);\n"
      "  end\n"
      "endmodule\n",
      "result");
  // 2.5 != 2 is true; a truncated integer comparison (2 != 2) would be false.
  EXPECT_EQ(result, 1u);
}

}  // namespace
