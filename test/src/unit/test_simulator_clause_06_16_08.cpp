// §6.16.8: Substr()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.8: substr(i, j) -- extract substring from index i to j
// =============================================================================
TEST(StringMethods, Substr) {
  StringFixture f;
  f.CreateStringVar("s", "hello world");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(6), f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "world");
}

}  // namespace
