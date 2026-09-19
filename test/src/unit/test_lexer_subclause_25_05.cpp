#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(InterfaceModport, ModportKeyword) {
  auto r = LexOne("modport");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModport);
}

}  // namespace
