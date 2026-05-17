#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SystemNameLexing, MaxLengthOk) {
  std::string id = "$" + std::string(1023, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(SystemNameLexing, ExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

}
