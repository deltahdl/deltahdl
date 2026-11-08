#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(EscapedIdentifierPreprocessor,
     EscapedIdentifierPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\my+sig"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor,
     EscapedKeywordPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\module ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\module"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, MultipleEscapedIdentifiersPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\a+b , \\c-d ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\a+b"), std::string::npos);
  EXPECT_NE(result.find("\\c-d"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedIdentifierInMacroContext) {
  PreprocFixture f;
  Preprocess(
      "`define SIG \\my+sig\n"
      "module t;\n"
      "  logic `SIG ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EscapedIdentifierPreprocessor, CommentOpenerInsideEscapedNameInMacroText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M \\a//b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x \\a//b y"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, QuoteInsideEscapedNameInMacroText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M \\a\"b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x \\a\"b y"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedMacroNameIsTheSimpleName) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define \\cpu3 1\n"
      "`ifdef cpu3\n"
      "FOUND\n"
      "`else\n"
      "MISSING\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("FOUND"), std::string::npos);
  EXPECT_EQ(out.find("MISSING"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedMacroUsageFindsTheSimpleName) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define cpu3 7\n"
      "x `\\cpu3 y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x 7"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedNameAfterOtherMacroText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M x \\a//b y\n"
      "`M\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x \\a//b y"), std::string::npos);
}

}  // namespace
