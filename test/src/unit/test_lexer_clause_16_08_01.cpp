#include <gtest/gtest.h>

#include "lexer/keywords.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(UntypedKeyword, RecognizedAsKwUntyped) {
  // §16.8.1: the keyword `untyped` names the formal-argument data type that
  // marks the formal as truly untyped. The lexer must recognize it as a
  // dedicated keyword token, not as a plain identifier — otherwise the
  // parser cannot distinguish "untyped" from a user type alias.
  auto kind = LookupKeyword("untyped");
  ASSERT_TRUE(kind.has_value());
  EXPECT_EQ(kind.value(), TokenKind::kKwUntyped);
}

}  // namespace
