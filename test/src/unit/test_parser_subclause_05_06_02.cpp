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

// 5.6.2: a keyword preceded by an escape (backslash) character is not
// interpreted as a keyword, so \begin does not open a sequential block. The
// §5.6.1 file carries the complementary rule that it is instead treated as a
// user-defined identifier.
TEST(LexicalConventionParsing, EscapedKeywordNotInterpretedAsKeyword) {
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(LexicalConventionParsing, AllUppercaseUsedAsIdentifier) {
  EXPECT_TRUE(ParseOk("module m; logic MODULE; endmodule"));
}

}  // namespace
