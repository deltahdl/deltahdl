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

// §5.6.1: an escaped identifier holds any printable character up to the white
// space ending it, so the `//` in `\a//b` opens no comment in macro text.
// Read as one, it cut the text to `\a`.
TEST(EscapedIdentifierPreprocessor, CommentOpenerInsideEscapedNameInMacroText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M \\a//b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x \\a//b y"), std::string::npos);
}

// Nor does a `"` inside one open a string literal in macro text, which was
// reported as an unterminated string.
TEST(EscapedIdentifierPreprocessor, QuoteInsideEscapedNameInMacroText) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M \\a\"b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x \\a\"b y"), std::string::npos);
}

// The backslash is no part of the identifier, so a macro defined as `\cpu3`
// is the macro `cpu3`, and `ifdef cpu3 finds it.
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

// And a usage written escaped finds a macro defined with the simple name.
TEST(EscapedIdentifierPreprocessor, EscapedMacroUsageFindsTheSimpleName) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define cpu3 7\n"
      "x `\\cpu3 y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("x 7"), std::string::npos);
}

// An escaped identifier inside macro text, after other tokens, is stepped over
// whole just as one opening the text is.
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
