// §6.16.11: Itoa()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.11: itoa(i) -- assign decimal string representation to variable
// =============================================================================
TEST(StringMethods, Itoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(123)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "123");
}

}  // namespace
