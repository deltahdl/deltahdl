#include "fixture_elaborator.h"

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

// §11.10: a string literal is a constant number, so it shall fold at
// elaboration when it initializes a localparam. "AB" packs to the 16-bit
// number 0x4142 (first character in the most-significant byte).
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

// A single-character literal folds to the 8-bit ASCII code of that character.
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

// §11.10: an operator manipulating a string literal operand behaves as though
// the literal were a single numeric value, and that holds in a constant
// expression evaluated at elaboration. "A" (65) + 1 folds to 66.
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

// A localparam folded from a string literal is itself a constant number that a
// second constant expression can consume (11.2.1 constant forms). A = "A" is
// 65, so B = A + 1 folds to 66, proving the folded value flows into the
// constant-expression scope rather than being dropped as unresolved.
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

// The constant-number rule holds for the `parameter` form as well as the
// `localparam` form; both take the parameter-resolution path. "AB" folds to the
// packed 16-bit constant 0x4142.
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

// A literal written with §5.9 hex escapes folds at elaboration to the same
// constant number as the plain-character form: "\x41\x42" packs to 0x4142,
// exercising the constant-expression escape-decoding path.
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

}  // namespace
