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

// §6.16.3: getc out of bounds returns 0.
TEST(StringMethods, GetcOutOfBounds) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §6.16.3: getc negative index returns 0.
TEST(StringMethods, GetcNegativeIndex) {
  StringFixture f;
  f.CreateStringVar("s", "hi");
  auto* neg = f.MakeIntLiteral(-1);
  auto* call = f.MakeMethodCall("s", "getc", {neg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
