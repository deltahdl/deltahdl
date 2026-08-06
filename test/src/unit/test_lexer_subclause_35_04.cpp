#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §35.4: "The leading backslash ( \ ) character and the trailing white space
// shall be stripped off by the SystemVerilog tool to create the linkage
// identifier." The lexer carries out the strip, and the resulting token text
// is what later passes use as the DPI linkage name.

TEST(DpiLinkageNameLexing, EscapedFormStripsBackslashAndTrailingSpace) {
  auto r = LexOne("\\foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "foo");
}

}  // namespace
