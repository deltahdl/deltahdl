#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, DefineAndUndef) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define FOO 1\n"
                              "module t;\n"
                              "endmodule\n"
                              "`undef FOO\n"));
}

TEST(CompilerDirectiveParsing, UndefThenRedefineProducesValidParse) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 8\n"
                              "`undef WIDTH\n"
                              "`define WIDTH 16\n"
                              "module t;\n"
                              "  parameter P = `WIDTH;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, UndefExcludesConditionalFromParse) {
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

}  // namespace
