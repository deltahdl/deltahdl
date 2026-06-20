#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringLiteralExpressionsSim, SingleCharStringLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] ch;\n"
      "  initial ch = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("ch");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41u);
}

TEST(StringLiteralExpressionsSim, StringLiteralCopyPaddedWithZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*8:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x4869ULL);
}

TEST(StringLiteralExpressionsSim, MultiCharStringLiteralAsciiValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x4142u);
}

TEST(StringLiteralExpressionsSim, StringLiteralWidthIs8PerChar) {
  SimFixture f;
  auto* e1 = ParseExprFrom("\"A\"", f);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(EvalExpr(e1, f.ctx, f.arena).width, 8u);

  auto* e3 = ParseExprFrom("\"ABC\"", f);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(EvalExpr(e3, f.ctx, f.arena).width, 24u);
}

TEST(StringLiteralExpressionsSim, StringLiteralArithmeticAdd) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" + 8'd1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x42u);
}

TEST(StringLiteralExpressionsSim, StringLiteralBitwiseOr) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" | 8'h20", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x61u);
}

TEST(StringLiteralExpressionsSim, StringLiteralRelationalGreater) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"B\" > \"A\"", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 1u);
}

TEST(StringLiteralExpressionsSim, StringLiteralShiftLeft) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"A\" << 1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x82u);
}

// A multi-character literal taking part in an operation is handled as one
// numeric value formed from all of its ASCII bytes, not byte-by-byte: "AB"
// is the 16-bit number 0x4142, so adding one yields 0x4143.
TEST(StringLiteralExpressionsSim, MultiCharStringLiteralActsAsSingleNumber) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"AB\" + 16'd1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x4143u);
}

// Left zero-padding of an oversized target must extend past a single 64-bit
// word: a 16-bit literal stored into an 80-bit vector keeps its bytes in the
// low word and leaves the entire upper word as padding zeros.
TEST(StringLiteralExpressionsSim, WideVectorPaddingSpansMultipleWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 80u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x4869ULL);
  EXPECT_EQ(var->value.words[1].aval, 0ULL);
}

}  // namespace
