// §22.13: `__FILE__ and `__LINE__

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection22, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Error at %s, line %d.\",\n"
              "    `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer line_num;\n"
              "  initial line_num = `__LINE__;\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileDirectiveInStringConcat) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"source: %s:%0d\", `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

}  // namespace
