#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Hextoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "hextoa", {f.MakeIntLiteral(255)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "ff");
}

}  // namespace
