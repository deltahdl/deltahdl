#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayOrdering, SortAscending) {
  SimFixture f;
  MakeDynArray(f, "arr", {40, 10, 30, 20});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(ArrayOrdering, SortAlreadySorted) {
  SimFixture f;
  MakeDynArray(f, "arr", {1, 2, 3, 4});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 1u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
  EXPECT_EQ(q->elements[2].ToUint64(), 3u);
  EXPECT_EQ(q->elements[3].ToUint64(), 4u);
}

TEST(ArrayOrdering, SortSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(ArrayOrdering, SortEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(ArrayOrdering, SortDuplicateValues) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 30, 10});
  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

TEST(ArrayOrdering, SortFixedArray) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray("arr", info);
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    MakeVar(f, name, 32, 0);
  }
  f.ctx.FindVariable("arr[0]")->value = MakeLogic4VecVal(f.arena, 32, 30);
  f.ctx.FindVariable("arr[1]")->value = MakeLogic4VecVal(f.arena, 32, 10);
  f.ctx.FindVariable("arr[2]")->value = MakeLogic4VecVal(f.arena, 32, 20);

  TryExecArrayPropertyStmt("arr", "sort", f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 30u);
}

TEST(ArrayOrdering, RsortDescending) {
  SimFixture f;
  MakeDynArray(f, "arr", {40, 10, 30, 20});
  TryExecArrayPropertyStmt("arr", "rsort", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 40u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
  EXPECT_EQ(q->elements[3].ToUint64(), 10u);
}

TEST(ArrayOrdering, RsortFixedArray) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray("arr", info);
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    MakeVar(f, name, 32, 0);
  }
  f.ctx.FindVariable("arr[0]")->value = MakeLogic4VecVal(f.arena, 32, 10);
  f.ctx.FindVariable("arr[1]")->value = MakeLogic4VecVal(f.arena, 32, 30);
  f.ctx.FindVariable("arr[2]")->value = MakeLogic4VecVal(f.arena, 32, 20);

  TryExecArrayPropertyStmt("arr", "rsort", f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 30u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 10u);
}

TEST(ArrayOrdering, ReverseOrder) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 10u);
}

TEST(ArrayOrdering, ReverseSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(ArrayOrdering, ReverseEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(ArrayOrdering, ReverseTwiceRestoresOriginal) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(ArrayOrdering, ReverseFixedArray) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray("arr", info);
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    MakeVar(f, name, 32, 0);
  }
  f.ctx.FindVariable("arr[0]")->value = MakeLogic4VecVal(f.arena, 32, 0xAA);
  f.ctx.FindVariable("arr[1]")->value = MakeLogic4VecVal(f.arena, 32, 0xBB);
  f.ctx.FindVariable("arr[2]")->value = MakeLogic4VecVal(f.arena, 32, 0xCC);

  TryExecArrayPropertyStmt("arr", "reverse", f.ctx, f.arena);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

TEST(ArrayOrdering, ShufflePreservesElements) {
  SimFixtureSeeded f;
  auto* q = f.ctx.CreateQueue("arr", 32);
  for (uint64_t v : {10u, 20u, 30u, 40u, 50u}) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = 5;
  f.ctx.RegisterArray("arr", info);
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 5u);

  uint64_t sum = 0;
  for (auto& e : q->elements) sum += e.ToUint64();
  EXPECT_EQ(sum, 150u);
}

TEST(ArrayOrdering, ShuffleEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(ArrayOrdering, ShuffleSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  TryExecArrayPropertyStmt("arr", "shuffle", f.ctx, f.arena);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(ArrayOrdering, SortViaMethodCall) {
  SimFixture f;
  MakeDynArray(f, "arr", {30, 10, 20});
  auto* call = MakeMethodCall(f.arena, "arr", "sort", {});
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(ArrayOrdering, RsortViaMethodCall) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 30, 20});
  auto* call = MakeMethodCall(f.arena, "arr", "rsort", {});
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 10u);
}

TEST(ArrayOrdering, ReverseViaMethodCall) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "arr", "reverse", {});
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 10u);
}

TEST(ArrayOrdering, ShuffleViaMethodCall) {
  SimFixtureSeeded f;
  auto* q = f.ctx.CreateQueue("arr", 32);
  for (uint64_t v : {10u, 20u, 30u}) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = 3;
  f.ctx.RegisterArray("arr", info);

  auto* call = MakeMethodCall(f.arena, "arr", "shuffle", {});
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  EXPECT_EQ(q->elements.size(), 3u);
  uint64_t sum = 0;
  for (auto& e : q->elements) sum += e.ToUint64();
  EXPECT_EQ(sum, 60u);
}

// §7.12.2: sort() may optionally order by the expression in a with clause
// instead of the raw element value. Sorting {3, 1, 2} ascending by the key
// (10 - item) inverts the natural element order, so the result proves the
// with expression — not the element value — drives the comparison.
TEST(ArrayOrdering, SortWithExprUsesExpression) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* call = MakeMethodCall(f.arena, "arr", "sort", {});
  call->with_expr = MakeBinary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 10),
                               MakeId(f.arena, "item"));
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 3u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
  EXPECT_EQ(q->elements[2].ToUint64(), 1u);
}

// §7.12.2: rsort() applies the same optional with-clause ordering but ranks
// keys in descending order. With key (10 - item), the descending key order
// recovers the natural ascending element order, again confirming the with
// expression governs the sort.
TEST(ArrayOrdering, RsortWithExprUsesExpression) {
  SimFixture f;
  MakeDynArray(f, "arr", {3, 1, 2});
  auto* call = MakeMethodCall(f.arena, "arr", "rsort", {});
  call->with_expr = MakeBinary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 10),
                               MakeId(f.arena, "item"));
  bool ok = TryExecArrayMethodStmt(call, f.ctx, f.arena);
  ASSERT_TRUE(ok);
  auto* q = f.ctx.FindQueue("arr");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 1u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
  EXPECT_EQ(q->elements[2].ToUint64(), 3u);
}

}  // namespace
