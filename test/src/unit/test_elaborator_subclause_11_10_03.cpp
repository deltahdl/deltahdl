#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
