#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(DpiLinkageNameLexing, EscapedFormStripsBackslashAndTrailingSpace) {
  auto r = LexOne("\\foo ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "foo");
}

}  // namespace
