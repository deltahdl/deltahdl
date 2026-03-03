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

}  // namespace
