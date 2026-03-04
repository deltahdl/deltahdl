#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, LetIdentifier_Escaped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let \\my+let = 1;\n"
              "endmodule\n"));
}

TEST(ParserA84, PrimaryEscapedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh50601, EscapedIdentifierAsName) {

  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserCh50601, EscapedKeywordAsIdentifier) {

  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Keyword) {

  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_SpecialChars) {

  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_ForwardSlash) {

  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Braces) {

  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

TEST(ParserCh50602, Keyword_EscapedAsIdentifier) {

  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

}
