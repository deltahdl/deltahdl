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

// The substr prototype returns a string, so the result must be a string-typed
// value whose width tracks its character count (8 bits per character), not a
// fixed-width integer.
TEST(StringMethods, SubstrReturnsStringType) {
  StringFixture f;
  f.CreateStringVar("s", "hello world");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(6), f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 40u);
}

TEST(StringMethods, SubstrNegativeI) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(-1), f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

TEST(StringMethods, SubstrJLessThanI) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(3), f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

TEST(StringMethods, SubstrJBeyondLength) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

TEST(StringMethods, SubstrEntireString) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral(4)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

TEST(StringMethods, SubstrSingleCharacter) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(2), f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "l");
}

TEST(StringMethods, SubstrEmptyString) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

}  // namespace
