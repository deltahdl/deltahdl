#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(SystemTfCallLexing, TypenameTokenizesAsSystemIdentifier) {
  auto r = LexOne("$typename");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$typename");
}

}  // namespace
