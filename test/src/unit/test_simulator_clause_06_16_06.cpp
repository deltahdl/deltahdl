#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(StringMethods, CompareEqual) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abc");

  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

TEST(StringMethods, CompareLessThan) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abd");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);

  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_LT(signed_val, 0);
}

}
