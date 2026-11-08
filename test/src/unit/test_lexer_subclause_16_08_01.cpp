#include <gtest/gtest.h>

#include "lexer/keywords.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(UntypedKeyword, RecognizedAsKwUntyped) {
  const auto kKind = LookupKeyword("untyped");
  ASSERT_TRUE(kKind.has_value());
  if (!kKind.has_value()) return;
  EXPECT_EQ(*kKind, TokenKind::kKwUntyped);
}

}  // namespace
