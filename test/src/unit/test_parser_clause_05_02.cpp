// §5.2: Lexical tokens

#include "fixture_parser.h"

using namespace delta;

namespace {

// =========================================================================
// From test_parser_clause_05.cpp — §5.1 General
// =========================================================================
TEST(ParserCh501, FreeFormatLayout) {
  // Spaces and newlines are not syntactically significant (except in
  // escaped identifiers and string literals). Tokens can be on one line.
  EXPECT_TRUE(ParseOk("module t; logic a; endmodule"));
}

TEST(ParserCh501, FreeFormatMultiline) {
  // Same construct spread over many lines.
  EXPECT_TRUE(
      ParseOk("module\n"
              "  t\n"
              ";\n"
              "  logic\n"
              "    a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, AllTokenTypesPresent) {
  // §5.1 lists: white space, comments, operators, numbers, string
  // literals, identifiers, keywords. This test exercises them all.
  EXPECT_TRUE(
      ParseOk("module t; // one-line comment\n"
              "  /* block comment */\n"
              "  logic [7:0] data = 8'hAB;\n"
              "  initial $display(\"hello\");\n"
              "endmodule\n"));
}

}  // namespace
