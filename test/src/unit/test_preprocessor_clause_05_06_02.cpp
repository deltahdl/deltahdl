#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(KeywordPreprocessor, KeywordPassesThroughPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  assign x = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST(KeywordPreprocessor, UppercaseKeywordAsIdentifierPassesThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic [7:0] MODULE;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("MODULE"), std::string::npos);
}

TEST(KeywordPreprocessor, MixedCaseKeywordAsIdentifierPassesThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic [7:0] Begin;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("Begin"), std::string::npos);
}

TEST(KeywordPreprocessor, KeywordInMacroExpansion) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define BLOCK begin\n"
      "module t;\n"
      "  initial `BLOCK\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(KeywordPreprocessor, EscapedKeywordPreservedInPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic [7:0] \\begin ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\\begin"), std::string::npos);
}

}  // namespace
