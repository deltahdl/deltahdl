#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

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

TEST(StringMethods, PutcNegativeIndex) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "abc");

  auto* call = f.MakeMethodCall(
      "s", "putc",
      {f.MakeIntLiteral(static_cast<uint64_t>(-1)), f.MakeIntLiteral('X')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "abc");
}

// §6.16.2: the out-of-bounds guard is i >= str.len(), so an index equal to the
// length is itself out of bounds (valid indices run 0..len-1). Exercise that
// exact boundary to pin the production guard against an off-by-one.
TEST(StringMethods, PutcIndexEqualsLength) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(5), f.MakeIntLiteral('X')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "hello");
}

// §6.16.2: str.putc(j, x) is defined to be semantically equivalent to the
// indexed character assignment str[j] = x. Drive both paths on identical
// strings and confirm they land the same result at the same position.
TEST(StringMethods, PutcEquivalentToIndexedAssign) {
  StringFixture f;
  auto* via_putc = f.CreateStringVar("s", "hello");
  auto* via_index = f.CreateStringVar("t", "hello");

  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(1), f.MakeIntLiteral('a')});
  EvalExpr(call, f.ctx, f.arena);

  auto* lhs =
      MakeSelectExpr(f.arena, MakeId(f.arena, "t"), MakeInt(f.arena, 1));
  auto rhs = EvalExpr(f.MakeIntLiteral('a'), f.ctx, f.arena);
  PerformBlockingAssign(lhs, rhs, f.ctx, f.arena);

  EXPECT_EQ(VecToString(via_putc->value), "hallo");
  EXPECT_EQ(VecToString(via_putc->value), VecToString(via_index->value));
}

}  // namespace
