// §22.14.2: IEEE Std 1364-1995 keywords

#include <gtest/gtest.h>

#include "lexer/keywords.h"
#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1364_1995_ModuleIsKeyword) {
  auto kw = LookupKeyword("module", KeywordVersion::kVer13641995);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwModule));
}

TEST(Lexer, KeywordVersion_1364_1995_AutomaticIsNotKeyword) {
  // "automatic" was introduced in 1364-2001.
  auto kw = LookupKeyword("automatic", KeywordVersion::kVer13641995);
  EXPECT_FALSE(kw.has_value());
}

}  // namespace
