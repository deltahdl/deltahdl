#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Putc) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral('H')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "Hello");
}

TEST(StringMethods, PutcOutOfBounds) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(5), f.MakeIntLiteral('X')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "abc");
}

TEST(StringMethods, PutcZeroByte) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "abc");
  auto* call =
      f.MakeMethodCall("s", "putc", {f.MakeIntLiteral(0), f.MakeIntLiteral(0)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "abc");
}

}
