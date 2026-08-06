#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, DefineSimpleMacro) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 8\n"
                              "module t;\n"
                              "  logic [`WIDTH-1:0] data;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, FunctionLikeMacroProducesValidAST) {
  auto r = ParseWithPreprocessor(
      "`define MAX(a,b) ((a) > (b) ? (a) : (b))\n"
      "module t;\n"
      "  parameter P = `MAX(3, 7);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilerDirectiveParsing, MultiLineMacroProducesValidAST) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define DECL(name, width) \\\n"
                              "  logic [width-1:0] name\n"
                              "module t;\n"
                              "  `DECL(bus, 8);\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, RedefinedMacroUsesLatestForParsing) {
  auto r = ParseWithPreprocessor(
      "`define VAL 10\n"
      "`define VAL 20\n"
      "module t;\n"
      "  parameter P = `VAL;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilerDirectiveParsing, EmptyMacroBodyParsesCorrectly) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define EMPTY\n"
                              "module t;\n"
                              "  `EMPTY\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, TokenPasteProducesValidIdentifier) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define PORT(dir, name) dir name\n"
                              "module t(\n"
                              "  `PORT(input, clk)\n"
                              ");\n"
                              "endmodule\n"));
}

}  // namespace
