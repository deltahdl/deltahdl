#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(Elaboration, StringLiteralWiderVectorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, MultiCharStringLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, StringLiteralArithmeticElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [7:0] r;\n"
      "  initial r = \"A\" + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, StringLiteralBitwiseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [7:0] r;\n"
      "  initial r = \"A\" | 8'h20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, StringLiteralRelationalElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  initial r = \"B\" > \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, StringLiteralConstantFoldsToPackedAscii) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [8*2:1] P = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0x4142);
}

TEST(Elaboration, SingleCharStringLiteralConstantFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam P = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 65);
}

TEST(Elaboration, StringLiteralOperandFoldsInConstantExpr) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam P = \"A\" + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 66);
}

TEST(Elaboration, StringLiteralParamConsumedAsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam A = \"A\";\n"
      "  localparam B = A + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 66);
}

TEST(Elaboration, StringLiteralConstantFoldsOnParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [8*2:1] P = \"AB\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0x4142);
}

TEST(Elaboration, StringLiteralHexEscapeConstantFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [8*2:1] P = \"\\x41\\x42\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0x4142);
}

TEST(StringLiteralElaboration, LongStringLiteralKeepsItsLeadingCharacters) {
  EvalFixture f;
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("\"Hello world\" == \"Xello world\"", f)), 0);
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("\"Hello world\" == \"Hello world\"", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("\"Hello world\" >> 80", f)), 'H');
}

}  // namespace
