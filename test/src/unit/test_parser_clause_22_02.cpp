#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, DirectiveRemainderParsesAsValidCode) {
  auto r = ParseWithPreprocessor(
      "`define FOO 1\n"
      "`ifdef FOO\n"
      "module m1; endmodule\n"
      "`endif module m2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilerDirectiveParsing, DirectiveInMacroExpandedToValidAST) {
  auto r = ParseWithPreprocessor(
      "`define DECLARE_MOD(name) module name; endmodule\n"
      "`DECLARE_MOD(m1)\n"
      "`DECLARE_MOD(m2)\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilerDirectiveParsing, DirectiveSupersededAcrossModules) {
  auto r = ParseWithPreprocessor(
      "`define VAL 1\n"
      "module m1;\n"
      "  localparam A = `VAL;\n"
      "endmodule\n"
      "`define VAL 2\n"
      "module m2;\n"
      "  localparam B = `VAL;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

TEST(CompilerDirectiveParsing, DirectiveInConditionalProducesValidAST) {
  auto r = ParseWithPreprocessor(
      "`define FEATURE 1\n"
      "module m;\n"
      "`ifdef FEATURE\n"
      "  localparam X = 1;\n"
      "`else\n"
      "  localparam X = 0;\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CompilerDirectiveParsing, DirectiveInCommentDoesNotAffectParse) {
  auto r = ParseWithPreprocessor(
      "// `define BAD syntax error!!\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
