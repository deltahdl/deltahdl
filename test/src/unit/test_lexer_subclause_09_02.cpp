#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(StructuredProcedureLexing, FinalKeyword) {
  auto r = LexOne("final ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFinal);
  EXPECT_EQ(r.token.text, "final");
}

TEST(StructuredProcedureLexing, InitialKeyword) {
  auto r = LexOne("initial ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInitial);
  EXPECT_EQ(r.token.text, "initial");
}

TEST(StructuredProcedureLexing, AlwaysKeyword) {
  auto r = LexOne("always ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlways);
  EXPECT_EQ(r.token.text, "always");
}

TEST(StructuredProcedureLexing, AlwaysCombKeyword) {
  auto r = LexOne("always_comb ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysComb);
  EXPECT_EQ(r.token.text, "always_comb");
}

TEST(StructuredProcedureLexing, AlwaysLatchKeyword) {
  auto r = LexOne("always_latch ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysLatch);
  EXPECT_EQ(r.token.text, "always_latch");
}

TEST(StructuredProcedureLexing, AlwaysFFKeyword) {
  auto r = LexOne("always_ff ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysFF);
  EXPECT_EQ(r.token.text, "always_ff");
}

TEST(StructuredProcedureLexing, KeywordsAreNotIdentifiers) {
  struct KeywordCase {
    const char* text;
    TokenKind kind;
  };
  const KeywordCase kKeywords[] = {
      {"initial", TokenKind::kKwInitial},
      {"always", TokenKind::kKwAlways},
      {"always_comb", TokenKind::kKwAlwaysComb},
      {"always_latch", TokenKind::kKwAlwaysLatch},
      {"always_ff", TokenKind::kKwAlwaysFF},
      {"final", TokenKind::kKwFinal},
  };
  for (const auto& kw : kKeywords) {
    std::string src = std::string(kw.text) + " ";
    auto r = LexOne(src);
    EXPECT_EQ(r.token.kind, kw.kind) << kw.text;
  }
}

}  // namespace
