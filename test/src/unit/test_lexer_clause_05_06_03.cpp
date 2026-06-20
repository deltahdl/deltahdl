#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.6.3: a name following the `$` is recognized as a system task/function
// identifier token. This observes the recognition rule directly, independent of
// the §5.6 length-limit checks below. The lexer makes no task-vs-function
// distinction, so a single recognition case covers the rule at this stage.
TEST(SystemNameLexing, NameLexesAsSystemIdentifier) {
  auto r = LexOne("$display");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

// §5.6.3 conditions the rule on a name *following* the `$`. When nothing
// name-like follows, the construct is not interpreted as a system
// task/function: the lexer emits a plain dollar token rather than a system
// identifier. This observes the negative branch of the recognition decision.
TEST(SystemNameLexing, BareDollarIsNotSystemIdentifier) {
  auto r = LexOne("$;");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
}

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

}  // namespace
