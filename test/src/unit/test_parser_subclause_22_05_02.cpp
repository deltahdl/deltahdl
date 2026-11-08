#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UndefParsing, UndefThenRedefineProducesValidParse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 8\n"
                              "`undef WIDTH\n"
                              "`define WIDTH 16\n"
                              "module t;\n"
                              "  parameter P = `WIDTH;\n"
                              "endmodule\n"));
}

TEST(UndefParsing, UndefExcludesConditionalFromParse) {
  auto result = ParseWithPreprocessor(
      "`define HAS_FEAT\n"
      "`undef HAS_FEAT\n"
      "`ifdef HAS_FEAT\n"
      "module feat; endmodule\n"
      "`endif\n"
      "module t; endmodule\n");
  EXPECT_FALSE(result.has_errors);
  EXPECT_EQ(result.cu->modules.size(), 1u);
  EXPECT_EQ(result.cu->modules[0]->name, "t");
}

TEST(UndefParsing, KeywordRunTogetherWithNameParsesAsMacroUsage) {
  auto result = ParseWithPreprocessor(
      "`define DECL logic [3:0] sig;\n"
      "`define undefDECL `DECL\n"
      "module t;\n"
      "`undefDECL\n"
      "endmodule\n");
  EXPECT_FALSE(result.has_errors);
  ASSERT_EQ(result.cu->modules.size(), 1u);
  EXPECT_FALSE(result.cu->modules[0]->items.empty());
}

}  // namespace
