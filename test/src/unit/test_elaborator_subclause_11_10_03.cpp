#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.10.3: the empty string literal is equivalent to the ASCII NUL character,
// i.e. a single byte whose value is zero. When it initializes a localparam the
// constant-expression folder therefore resolves the parameter to 0 (rather than
// dropping it as a zero-width nothing).
TEST(EmptyStringLiteralElab, EmptyStringLiteralFoldsToZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam P = \"\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0);
}

// §11.10.3 draws the value zero of the empty string apart from the string "0",
// whose single character is ASCII 0x30. The two literals fold to distinct
// constants, so the empty-string value is genuinely NUL and not a stand-in for
// the digit character.
TEST(EmptyStringLiteralElab, StringZeroFoldsToAsciiDigitValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam P = \"0\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0x30);
}

// §11.10.3: the empty string literal compares equal to an explicit NUL escape
// (§5.9). Folding ("" == "\0") in a constant expression yields true, observing
// that the constant-expression path treats the empty literal as the NUL byte.
TEST(EmptyStringLiteralElab, EmptyStringEqualsNulEscapeFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam E = (\"\" == \"\\0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 1);
}

// The empty-string-is-NUL rule holds for the `parameter` constant form as well
// as `localparam`; the two keywords reach parameter resolution by different
// paths, so the empty literal must fold to 0 for both. `parameter P = "";`
// therefore resolves to zero just like the localparam case.
TEST(EmptyStringLiteralElab, EmptyStringParameterFoldsToZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = \"\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0);
}

// The negative half of the rule: the empty string does not equal the string
// "0". Folding ("" == "0") yields false at elaboration, confirming the constant
// folder distinguishes the NUL value from the digit character.
TEST(EmptyStringLiteralElab, EmptyStringDiffersFromStringZeroFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam E = (\"\" == \"0\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 0);
}

}  // namespace
