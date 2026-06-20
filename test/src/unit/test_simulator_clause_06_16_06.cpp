#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

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

TEST(StringMethods, CompareGreaterThan) {
  StringFixture f;
  f.CreateStringVar("s", "abd");
  f.CreateStringVar("t", "abc");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_GT(signed_val, 0);
}

TEST(StringMethods, CompareBothEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  f.CreateStringVar("t", "");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

TEST(StringMethods, CompareEmptyVsNonEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  f.CreateStringVar("t", "abc");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_LT(signed_val, 0);
}

TEST(StringMethods, CompareCaseSensitive) {
  StringFixture f;
  f.CreateStringVar("s", "ABC");
  f.CreateStringVar("t", "abc");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_NE(signed_val, 0);
}

// The prototype declares "function int compare(string s)": the result is an
// int, which is a 32-bit value.
TEST(StringMethods, CompareReturnsIntWidth) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abd");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// strcmp ordering when one string is a proper prefix of the other: the shorter
// string compares less than the longer one even though no character differs.
TEST(StringMethods, ComparePrefixIsLessThanLonger) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abcd");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_LT(signed_val, 0);
}

// The reverse direction: the longer string compares greater than the prefix.
TEST(StringMethods, CompareLongerIsGreaterThanPrefix) {
  StringFixture f;
  f.CreateStringVar("s", "abcd");
  f.CreateStringVar("t", "abc");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_GT(signed_val, 0);
}

}  // namespace
