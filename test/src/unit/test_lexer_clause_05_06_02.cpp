// §5.6.2

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(Keywords, ModuleKeyword) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

}  // namespace
