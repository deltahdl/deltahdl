#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StringLenElaboration, LenOfAStringLocalparamFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abc\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

TEST(StringLenElaboration, LenOfTheEmptyStringFoldsToZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 0);
}

TEST(StringLenElaboration,
     LenOfAStringLongerThanSixtyFourBitsFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abcdefghi\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 9);
}

TEST(StringLenElaboration, LenCountsAnEscapeSequenceAsOneCharacter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\nb\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

TEST(StringLenElaboration, LenOfAStringParameterPortFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter string S = \"hello\") ();\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 5);
}

TEST(StringLenElaboration, LenOfAnIntegerParameterDoesNotFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int S = 3;\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_FALSE(n->is_resolved);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(StringLenElaboration, LenIgnoresANulEscapeInTheInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\0b\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 2);
}

TEST(StringLenElaboration, LenIgnoresAHexNulEscapeInTheInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"a\\x00b\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 2);
}

TEST(StringLenElaboration, LenOfAnAllNulInitializerIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"\\0\\0\";\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 0);
}

TEST(StringLenElaboration,
     LenOfAParameterInitializedFromAnotherParameterFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter string A = \"John Smith\";\n"
      "  parameter string B = A;\n"
      "  localparam int N = B.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 10);
}

TEST(StringLenElaboration,
     LenOfAGenerateBlockStringLocalparamFoldsToTheCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string S = \"abc\";\n"
      "      localparam int N = S.len();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 3);
}

TEST(StringLenElaboration,
     LenOfALoopGenerateBlockStringLocalparamFoldsInEveryIteration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    localparam string S = \"ab\";\n"
      "    localparam int N = S.len();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  int ns = 0;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name != "N") continue;
    ++ns;
    EXPECT_TRUE(param.is_resolved);
    EXPECT_EQ(param.resolved_value, 2);
  }
  EXPECT_EQ(ns, 2);
}

}  // namespace
