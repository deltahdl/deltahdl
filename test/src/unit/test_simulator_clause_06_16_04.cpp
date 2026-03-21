#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Toupper) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "HELLO");
}

TEST(StringMethods, ToupperEmptyString) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "");
}

TEST(StringMethods, ToupperAlreadyUppercase) {
  StringFixture f;
  f.CreateStringVar("s", "HELLO");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "HELLO");
}

TEST(StringMethods, ToupperMixedCase) {
  StringFixture f;
  f.CreateStringVar("s", "HeLLo");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "HELLO");
}

TEST(StringMethods, ToupperPreservesNonAlpha) {
  StringFixture f;
  f.CreateStringVar("s", "a1-b2!");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "A1-B2!");
}

TEST(StringMethods, ToupperOriginalUnchanged) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "toupper");
  EvalExpr(call, f.ctx, f.arena);
  auto* read = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto ch = EvalExpr(read, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('h'));
}

}  // namespace
