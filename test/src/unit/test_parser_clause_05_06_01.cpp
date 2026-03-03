// §5.6.1: Escaped identifiers

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

// =============================================================================
// A.8.4 Primaries — escaped identifier as primary
// =============================================================================
// § primary — escaped identifier
TEST(ParserA84, PrimaryEscapedIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  logic \\my-signal ;\n"
      "  initial \\my-signal = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// From test_parser_clause_05.cpp
TEST(ParserCh50601, EscapedIdentifierAsName) {
  // §5.6.1: escaped identifiers include special characters.
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserCh50601, EscapedKeywordAsIdentifier) {
  // §5.6.1: escaped keyword is treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50601, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Keyword) {
  // An escaped keyword is treated as a user-defined identifier, not as a
  // keyword. \net is a valid user-defined wire name.
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_SpecialChars) {
  // Escaped identifiers can contain any printable ASCII character.
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_ForwardSlash) {
  // \net1/\net2 is a valid escaped identifier containing a slash.
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

}  // namespace
