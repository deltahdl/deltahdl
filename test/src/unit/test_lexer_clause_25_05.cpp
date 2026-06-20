#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(InterfaceModport, ModportKeyword) {
  auto r = LexOne("modport");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModport);
}

}  // namespace
