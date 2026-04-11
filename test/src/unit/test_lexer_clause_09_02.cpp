#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(StructuredProcedureLexing, AlwaysKeyword) {
  auto r = LexOne("always ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlways);
  EXPECT_EQ(r.token.text, "always");
}

TEST(StructuredProcedureLexing, FinalKeyword) {
  auto r = LexOne("final ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFinal);
  EXPECT_EQ(r.token.text, "final");
}

TEST(StructuredProcedureLexing, KeywordsAreNotIdentifiers) {
  const char* keywords[] = {"initial",     "always",    "always_comb",
                             "always_latch", "always_ff", "final"};
  for (const auto* kw : keywords) {
    std::string src = std::string(kw) + " ";
    auto r = LexOne(src);
    EXPECT_NE(r.token.kind, TokenKind::kIdentifier) << kw;
  }
}

}  // namespace
