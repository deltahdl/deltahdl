#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Getc) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('e'));
}

TEST(StringMethods, GetcOutOfBounds) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, GetcNegativeIndex) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* neg = f.MakeIntLiteral(-1);
  auto* call = f.MakeMethodCall("s", "getc", {neg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, GetcFirstCharacter) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('a'));
}

TEST(StringMethods, GetcLastCharacter) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('c'));
}

TEST(StringMethods, GetcEmptyString) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(0)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
