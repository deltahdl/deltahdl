// §6.16.2: Putc()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.2: putc(i, c) -- replace byte at index i
// =============================================================================
TEST(StringMethods, Putc) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral('H')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "Hello");
}

}  // namespace
