#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, StringWithNewlineEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithTabEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"col1\\tcol2\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithQuoteEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithOctalEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\101\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithHexEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\x41\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithUnknownEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\b\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithBackslashEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\\\\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithLineContinuation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"AB\\\nCD\");\n"
              "endmodule"));
}

}  // namespace
