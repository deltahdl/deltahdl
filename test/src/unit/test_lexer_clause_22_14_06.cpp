// §22.14.6: IEEE Std 1800-2005 keywords

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(Lexer, KeywordVersion_1800_2005_LogicIsKeyword) {
  auto kw = LookupKeyword("logic", KeywordVersion::kVer18002005);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwLogic));
}

}  // namespace
