#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.6 prose: "Implementations may set a limit on the maximum length of
// identifiers, but the limit shall be at least 1024 characters."
TEST(SystemNameLexing, MaxLengthOk) {
  std::string id = "$" + std::string(1023, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

// §5.6 prose: max-length floor of 1024 — reporting an error past the floor.
TEST(SystemNameLexing, ExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

}  // namespace
