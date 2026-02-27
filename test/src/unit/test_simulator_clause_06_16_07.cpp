// §6.16.7: Icompare()

#include "fixture_string.h"

using namespace delta;

namespace {

// =============================================================================
// §6.16.7: icompare(s) -- case-insensitive compare
// =============================================================================
TEST(StringMethods, IcompareEqual) {
  StringFixture f;
  f.CreateStringVar("s", "Hello");
  f.CreateStringVar("t", "hello");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

}  // namespace
