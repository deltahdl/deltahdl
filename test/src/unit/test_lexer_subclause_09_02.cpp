#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(StructuredProcedureLexing, FinalKeyword) {
  auto r = LexOne("final ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFinal);
  EXPECT_EQ(r.token.text, "final");
}

// §9.2 enumerates six construct keywords; each must be recognized as its own
// keyword token, not just as "some non-identifier." One test per keyword form.
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

// §5.6 rules that a keyword may not be used as a user-defined identifier, and
// §9.2 makes these six the keywords of the structured procedures. Each source
// is paired with the one TokenKind §9.2 gives it, so the test fails when a
// keyword lexes as an identifier and equally when it lexes as another keyword:
// a table mapping all six onto one enumerator goes red here.
TEST(StructuredProcedureLexing, KeywordsAreNotIdentifiers) {
  struct KeywordCase {
    const char* text;
    TokenKind kind;
  };
  const KeywordCase keywords[] = {
      {"initial", TokenKind::kKwInitial},
      {"always", TokenKind::kKwAlways},
      {"always_comb", TokenKind::kKwAlwaysComb},
      {"always_latch", TokenKind::kKwAlwaysLatch},
      {"always_ff", TokenKind::kKwAlwaysFF},
      {"final", TokenKind::kKwFinal},
  };
  for (const auto& kw : keywords) {
    std::string src = std::string(kw.text) + " ";
    auto r = LexOne(src);
    EXPECT_EQ(r.token.kind, kw.kind) << kw.text;
  }
}

}  // namespace
