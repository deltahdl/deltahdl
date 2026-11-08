#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, StringWithNewlineEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithQuoteEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, StringWithBackslashEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\\\\");\n"
              "endmodule"));
}

}  // namespace
