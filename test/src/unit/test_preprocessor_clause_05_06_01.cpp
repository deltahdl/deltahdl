#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(EscapedIdentifierPreprocessor, EscapedIdentifierPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\my+sig"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedKeywordPreservedThroughPreprocessing) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\module ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\module"), std::string::npos);
}

TEST(EscapedIdentifierPreprocessor, EscapedIdentifierSpecialCharsPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\***error-condition*** ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\***error-condition***"), std::string::npos);
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
  auto result = Preprocess(
      "`define SIG \\my+sig\n"
      "module t;\n"
      "  logic `SIG ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EscapedIdentifierPreprocessor, EscapedIdentDashClockPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\-clock ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\-clock"), std::string::npos);
}

// §5.6.1: digit-leading body passes through the preprocessor verbatim.
TEST(EscapedIdentifierPreprocessor, EscapedIdentAllDigitsPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\1234 ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\1234"), std::string::npos);
}

// §5.6.1: case of body characters survives the preprocessor unchanged.
TEST(EscapedIdentifierPreprocessor, EscapedIdentPreservesCase) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic \\AbCdEf ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\AbCdEf"), std::string::npos);
}

}  // namespace
