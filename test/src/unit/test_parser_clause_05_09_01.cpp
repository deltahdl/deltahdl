// §5.9.1: Special characters in strings

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50901, StringEscape_Newline) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(ParserCh50901, StringEscape_Tab) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"col1\\tcol2\");\n"
              "endmodule"));
}

TEST(ParserCh50901, StringEscape_Quote) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

}  // namespace
