#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, LenEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, LenBasic) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
}

// §6.16.1 declares the prototype "function int len();": the result is an int,
// i.e. a 32-bit value, independent of how long the string is.
TEST(StringMethods, LenReturnsIntWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
