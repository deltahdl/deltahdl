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

}  // namespace
