#include "fixture_lexer.h"
#include "helpers_dotted_name_tokens.h"

using namespace delta;

namespace {

TEST(DottedNameLexing, TwoComponentDottedName) {
  auto tokens = Lex("a.b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(DottedNameLexing, ThreeComponentDottedName) {
  ExpectThreeComponentDottedNameTokens("a", "b", "c");
}

TEST(DottedNameLexing,
     DottedNameTokensIdenticalForMemberSelectAndHierarchical) {
  auto member_tokens = Lex("s.x");
  auto hier_tokens = Lex("inst.sig");
  ASSERT_GE(member_tokens.size(), 4u);
  ASSERT_GE(hier_tokens.size(), 4u);
  EXPECT_EQ(member_tokens[0].kind, hier_tokens[0].kind);
  EXPECT_EQ(member_tokens[1].kind, hier_tokens[1].kind);
  EXPECT_EQ(member_tokens[2].kind, hier_tokens[2].kind);
}

}  // namespace
