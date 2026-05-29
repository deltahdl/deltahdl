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

TEST(DpiLinkageNameLexing, EscapedKeywordYieldsBareKeywordText) {
  // §35.4: a global name that clashes with a SystemVerilog keyword shall be
  // written in escaped form. After stripping, the linkage identifier is the
  // bare keyword text, which on its own is a valid C identifier shape.
  auto r = LexOne("\\if ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "if");
}

TEST(DpiLinkageNameLexing, EscapedNameStrippedBeforeNonSpaceTerminator) {
  // The strip terminates at the first whitespace after the name; a following
  // operator becomes its own token and is not absorbed into the identifier.
  auto tokens = Lex("\\bar =");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "bar");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEq);
}

}  // namespace
