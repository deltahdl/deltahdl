#include "fixture_parser.h"

using namespace delta;

namespace {

// A backslash escape of an ordinary character is scanned as string content and
// does not terminate the literal; the argument parses as one string.
TEST(LexicalConventionParsing, StringWithNewlineEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

// An escaped double quote is content, so it must not close the string early.
TEST(LexicalConventionParsing, StringWithQuoteEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

// An escaped backslash is consumed as a single unit, so the following quote is
// the terminator rather than being treated as escaped.
TEST(LexicalConventionParsing, StringWithBackslashEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\\\\");\n"
              "endmodule"));
}

}  // namespace
