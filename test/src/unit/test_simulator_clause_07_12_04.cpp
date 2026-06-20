#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(ArrayIteratorIndex, DefaultIndexInFindIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});

  auto* pred = MakeBinary(f.arena, TokenKind::kGt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 0));
  auto* call = MakeMethodCall(f.arena, "arr", "find_index", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFind) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

  auto* pred = MakeBinary(f.arena, TokenKind::kLt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
  EXPECT_EQ(out[1].ToUint64(), 20u);
}

TEST(ArrayIteratorIndex, DefaultIndexInMap) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});

  auto* with_expr = MakeId(f.arena, "item.index");
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 0u);
  EXPECT_EQ(out[1].ToUint64(), 1u);
  EXPECT_EQ(out[2].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindFirst) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15, 20});

  auto* pred = MakeBinary(f.arena, TokenKind::kGtEq,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "arr", "find_first", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 15u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindLast) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15, 20});

  auto* pred = MakeBinary(f.arena, TokenKind::kLt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "arr", "find_last", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindFirstIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15, 20});

  auto* pred = MakeBinary(f.arena, TokenKind::kGt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "arr", "find_first_index", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindLastIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {5, 10, 15, 20});

  auto* pred = MakeBinary(f.arena, TokenKind::kLt,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 3));
  auto* call = MakeMethodCall(f.arena, "arr", "find_last_index", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, IndexEqualToItemValue) {
  SimFixture f;

  MakeDynArray(f, "arr", {2, 1, 2, 3});

  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "item"),
                          MakeId(f.arena, "item.index"));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, RenamedIndexArgument) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});

  auto* iter_arg = MakeId(f.arena, "elem");
  auto* idx_arg = MakeId(f.arena, "pos");

  auto* pred = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "elem.pos"),
                          MakeInt(f.arena, 2));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {iter_arg, idx_arg});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
  EXPECT_EQ(out[1].ToUint64(), 20u);
}

TEST(ArrayIteratorIndex, RenamedIndexInFindIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {100, 200, 300});

  auto* iter_arg = MakeId(f.arena, "x");
  auto* idx_arg = MakeId(f.arena, "i");

  auto* pred = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "x.i"),
                          MakeInt(f.arena, 0));
  auto* call =
      MakeMethodCall(f.arena, "arr", "find_index", {iter_arg, idx_arg});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0].ToUint64(), 1u);
  EXPECT_EQ(out[1].ToUint64(), 2u);
}

TEST(ArrayIteratorIndex, RenamedIndexInMap) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});

  auto* iter_arg = MakeId(f.arena, "a");
  auto* idx_arg = MakeId(f.arena, "idx");

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                               MakeId(f.arena, "a.idx"));
  auto* call = MakeMethodCall(f.arena, "arr", "map", {iter_arg, idx_arg});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].ToUint64(), 10u);
  EXPECT_EQ(out[1].ToUint64(), 21u);
  EXPECT_EQ(out[2].ToUint64(), 32u);
}

TEST(ArrayIteratorIndex, IndexReturnTypeIs32Bit) {
  SimFixture f;
  MakeDynArray(f, "arr", {42, 99, 7});

  auto* with_expr = MakeId(f.arena, "item.index");
  auto* call = MakeMethodCall(f.arena, "arr", "map", {});
  call->with_expr = with_expr;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0].width, 32u);
  EXPECT_EQ(out[1].width, 32u);
  EXPECT_EQ(out[2].width, 32u);
}

TEST(ArrayIteratorIndex, EmptyArrayIndexInFind) {
  SimFixture f;
  MakeDynArray(f, "arr", {});

  auto* pred = MakeBinary(f.arena, TokenKind::kGtEq,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 0));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 0u);
}

TEST(ArrayIteratorIndex, SingleElementIndex) {
  SimFixture f;
  MakeDynArray(f, "arr", {77});

  auto* pred = MakeBinary(f.arena, TokenKind::kEqEq,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 0));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0].ToUint64(), 77u);
}

TEST(ArrayIteratorIndex, IndexMatchesNoElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});

  auto* pred = MakeBinary(f.arena, TokenKind::kGtEq,
                          MakeId(f.arena, "item.index"), MakeInt(f.arena, 3));
  auto* call = MakeMethodCall(f.arena, "arr", "find", {});
  call->with_expr = pred;
  std::vector<Logic4Vec> out;
  bool ok = TryCollectLocatorResult(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.size(), 0u);
}

}  // namespace
