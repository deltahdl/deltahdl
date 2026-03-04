#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(StringMethods, Toupper) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "HELLO");
}

}
