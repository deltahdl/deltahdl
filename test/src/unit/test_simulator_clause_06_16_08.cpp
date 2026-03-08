#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Substr) {
  StringFixture f;
  f.CreateStringVar("s", "hello world");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(6), f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "world");
}

// §6.16.8: substr with out-of-bounds returns empty string.
TEST(StringMethods, SubstrOutOfBounds) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(10), f.MakeIntLiteral(15)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

}  // namespace
