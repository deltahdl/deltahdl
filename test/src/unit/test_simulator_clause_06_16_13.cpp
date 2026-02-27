// §6.16.13: Octtoa()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.13: octtoa(i) -- assign octal string representation to variable
// =============================================================================
TEST(StringMethods, Octtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(8)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "10");
}

}  // namespace
