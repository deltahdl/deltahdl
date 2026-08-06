#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(InterfaceItemsLexing, ExternKeyword) {
  auto r = LexOne("extern");
  EXPECT_EQ(r.token.kind, TokenKind::kKwExtern);
}

TEST(InterfaceItemsLexing, ForkjoinKeyword) {
  auto r = LexOne("forkjoin");
  EXPECT_EQ(r.token.kind, TokenKind::kKwForkjoin);
}

TEST(InterfaceItemsLexing, ExternForkjoinSequence) {
  auto tokens = Lex("extern forkjoin task");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExtern);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwForkjoin);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwTask);
}

TEST(InterfaceItemsLexing, InterfaceKeyword) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(InterfaceItemsLexing, EndinterfaceKeyword) {
  auto r = LexOne("endinterface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndinterface);
}

TEST(InterfaceItemsLexing, InterfaceKeywordSequence) {
  auto tokens = Lex("interface endinterface modport extern");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInterface);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndinterface);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwModport);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwExtern);
}

TEST(InterfaceItemsLexing, KeywordsNotIdentifiers) {
  auto tokens = Lex("extern my_func");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwExtern);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
