#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, KeywordsAreReserved) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "  logic l;\n"
              "  assign w = 0;\n"
              "  initial begin\n"
              "    if (l) w = 1;\n"
              "    else w = 0;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, UppercaseNotKeyword) {
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

TEST(LexicalConventionParsing, EscapedKeywordAsIdentifier) {
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

}  // namespace
