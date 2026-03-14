#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module t;\n"
                              "  initial $display(\"Error at %s, line %d.\",\n"
                              "    `__FILE__, `__LINE__);\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, LineDirectiveInAssignment) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module t;\n"
                              "  integer line_num;\n"
                              "  initial line_num = `__LINE__;\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, FileDirectiveInStringConcat) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module t;\n"
      "  initial $display(\"source: %s:%0d\", `__FILE__, `__LINE__);\n"
      "endmodule\n"));
}

TEST(CompilerDirectiveParsing, FileDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module t;\n"
                              "  initial $display(\"File: %s\", `__FILE__);\n"
                              "endmodule\n"));
}

TEST(CompilerDirectiveParsing, LineDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module t;\n"
                              "  initial $display(\"Line: %0d\", `__LINE__);\n"
                              "endmodule\n"));
}

}  // namespace
