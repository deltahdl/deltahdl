#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

TEST(StringMethods, IcompareLessThan) {
  StringFixture f;
  f.CreateStringVar("s", "ABC");
  f.CreateStringVar("t", "def");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_LT(signed_val, 0);
}

TEST(StringMethods, IcompareGreaterThan) {
  StringFixture f;
  f.CreateStringVar("s", "def");
  f.CreateStringVar("t", "ABC");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_GT(signed_val, 0);
}

TEST(StringMethods, IcompareBothEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  f.CreateStringVar("t", "");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

TEST(StringMethods, IcompareSameCase) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  f.CreateStringVar("t", "hello");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

}  // namespace
