#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringLiteralExpressionsSim, SingleCharStringLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] ch;\n"
      "  initial ch = \"A\";\n"
      "endmodule\n",
      f, "ch");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41u);
}

TEST(StringLiteralExpressionsSim, MultiCharStringLiteralAsciiValues) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f, "s");
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

TEST(StringLiteralExpressionsSim, MultiCharStringLiteralActsAsSingleNumber) {
  SimFixture f;
  auto* expr = ParseExprFrom("\"AB\" + 16'd1", f);
  ASSERT_NE(expr, nullptr);
  auto val = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(val.ToUint64(), 0x4143u);
}

TEST(StringLiteralExpressionsSim, WideVectorPaddingSpansMultipleWords) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 80u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x4869ULL);
  EXPECT_EQ(var->value.words[1].aval, 0ULL);
}

TEST(StringLiteralExpressionsSim,
     StringLiteralEscapeSequencesArePackedAsAscii) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"\\t!\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0921ULL);
}

TEST(StringLiteralExpressionsSim, StringLiteralTruncatedIntoNarrowVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42ULL);
}

TEST(StringLiteralExpressionsSim, StringLiteralInContinuousAssignment) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = \"A\";\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41ULL);
}

TEST(StringLiteralExpressionsSim, HeadExampleConcatenateAndStore) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module string_test;\n"
      "  bit [8*14:1] stringvar;\n"
      "  initial begin\n"
      "    stringvar = \"Hello world\";\n"
      "    stringvar = {stringvar, \"!!!\"};\n"
      "  end\n"
      "endmodule\n",
      f, "stringvar");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 112u);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x776f726c64212121ULL);
  EXPECT_EQ(var->value.words[1].aval, 0x48656c6c6f20ULL);
}

TEST(StringLiteralExpressionsSim, PaddingConsistentWithNonstringUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*4:1] a, b;\n"
      "  initial begin\n"
      "    a = \"Hi\";\n"
      "    b = 16'h4869;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x4869ULL);
  EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64());
}

}  // namespace
