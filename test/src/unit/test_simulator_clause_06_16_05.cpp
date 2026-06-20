#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Tolower) {
  StringFixture f;
  f.CreateStringVar("s", "HELLO");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

TEST(StringMethods, TolowerEmptyString) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

TEST(StringMethods, TolowerAlreadyLowercase) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

TEST(StringMethods, TolowerMixedCase) {
  StringFixture f;
  f.CreateStringVar("s", "HeLLo");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

TEST(StringMethods, TolowerPreservesNonAlpha) {
  StringFixture f;
  f.CreateStringVar("s", "A1-B2!");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "a1-b2!");
}

TEST(StringMethods, TolowerOriginalUnchanged) {
  StringFixture f;
  f.CreateStringVar("s", "HELLO");
  auto* call = f.MakeMethodCall("s", "tolower");
  EvalExpr(call, f.ctx, f.arena);
  auto* read = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto ch = EvalExpr(read, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('H'));
}

}  // namespace
