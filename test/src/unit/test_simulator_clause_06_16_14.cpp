// §6.16.14: Bintoa()

#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.14: bintoa(i) -- assign binary string representation to variable
// =============================================================================
TEST(StringMethods, Bintoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(10)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "1010");
}

}  // namespace
