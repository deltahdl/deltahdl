// §6.16.5: Tolower()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.5: tolower() -- returns lowercased copy
// =============================================================================
TEST(StringMethods, Tolower) {
  StringFixture f;
  f.CreateStringVar("s", "HELLO");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

}  // namespace
