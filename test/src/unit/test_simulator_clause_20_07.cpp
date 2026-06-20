#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SysTask, LeftReturnsUpperBound) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$left", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RightReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$right", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, LowReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$low", {MkInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, DimensionsOfUnpackedArray) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 4;
  info.elem_width = 32;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 32);
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "arr")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

TEST(SysTask, UnpackedDimensionsOfArray) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 4;
  info.elem_width = 32;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 32);
  auto* expr =
      MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "arr")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(SysTask, DimensionsOfScalar) {
  SysTaskFixture f;
  f.ctx.CreateVariable("x", 8);
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

TEST(SysTask, UnpackedDimensionsOfScalar) {
  SysTaskFixture f;
  f.ctx.CreateVariable("x", 8);
  auto* expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(SysTask, DimensionsOfQueue) {
  SysTaskFixture f;
  f.ctx.CreateQueue("q", 16, -1);
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

TEST(SysTask, UnpackedDimensionsOfQueue) {
  SysTaskFixture f;
  f.ctx.CreateQueue("q", 16, -1);
  auto* expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

// §20.7: for a queue or dynamic array dimension $left returns 0, $increment
// returns -1, and $size/$right reflect the current element count.
TEST(SysTask, QueueLeftReturnsZero) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 2));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 3));
  auto* expr = MkSysCall(f.arena, "$left", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(SysTask, QueueRightReturnsSizeMinusOne) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 2));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 3));
  auto* expr = MkSysCall(f.arena, "$right", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

TEST(SysTask, QueueIncrementReturnsMinusOne) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  auto* expr = MkSysCall(f.arena, "$increment", {MkId(f.arena, "q")});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(expr, f.ctx, f.arena).ToUint64()),
            -1);
}

TEST(SysTask, QueueSizeReturnsElementCount) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 2));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 3));
  auto* expr = MkSysCall(f.arena, "$size", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 3u);
}

// §20.7: $right of an empty queue/dynamic array dimension is -1.
TEST(SysTask, EmptyQueueRightReturnsMinusOne) {
  SysTaskFixture f;
  f.ctx.CreateQueue("q", 16, -1);
  auto* expr = MkSysCall(f.arena, "$right", {MkId(f.arena, "q")});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(expr, f.ctx, f.arena).ToUint64()),
            -1);
}

// §20.7: on an integral-indexed associative array dimension $left is 0,
// $increment is -1, and $size is the number of elements currently allocated.
TEST(SysTask, AssocLeftReturnsZero) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  auto* expr = MkSysCall(f.arena, "$left", {MkId(f.arena, "a")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(SysTask, AssocIncrementReturnsMinusOne) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  auto* expr = MkSysCall(f.arena, "$increment", {MkId(f.arena, "a")});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(expr, f.ctx, f.arena).ToUint64()),
            -1);
}

TEST(SysTask, AssocSizeReturnsAllocatedCount) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  a->int_data[9] = MakeLogic4VecVal(f.arena, 32, 90);
  auto* expr = MkSysCall(f.arena, "$size", {MkId(f.arena, "a")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

// §20.7: $low/$high report the lowest/largest currently allocated index.
TEST(SysTask, AssocLowReturnsLowestIndex) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  a->int_data[9] = MakeLogic4VecVal(f.arena, 32, 90);
  auto* expr = MkSysCall(f.arena, "$low", {MkId(f.arena, "a")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 3u);
}

TEST(SysTask, AssocHighReturnsHighestIndex) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  a->int_data[9] = MakeLogic4VecVal(f.arena, 32, 90);
  auto* expr = MkSysCall(f.arena, "$high", {MkId(f.arena, "a")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 9u);
}

// §20.7: $right of an associative array dimension is the highest possible
// index value for the integral index type.
TEST(SysTask, AssocRightReturnsHighestIndexValue) {
  SysTaskFixture f;
  auto* a = f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                                   AssocArraySpec{/*index_width=*/8});
  a->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);
  auto* expr = MkSysCall(f.arena, "$right", {MkId(f.arena, "a")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 255u);
}

// §20.7: $low/$high of an associative array with no allocated elements is 'x.
TEST(SysTask, EmptyAssocLowReturnsUnknown) {
  SysTaskFixture f;
  f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                         AssocArraySpec{/*index_width=*/8});
  auto* expr = MkSysCall(f.arena, "$low", {MkId(f.arena, "a")});
  EXPECT_FALSE(EvalExpr(expr, f.ctx, f.arena).IsKnown());
}

// §20.7: $high of an associative array with no allocated elements is likewise
// 'x (no largest allocated index exists to report).
TEST(SysTask, EmptyAssocHighReturnsUnknown) {
  SysTaskFixture f;
  f.ctx.CreateAssocArray("a", 32, /*is_string_key=*/false,
                         AssocArraySpec{/*index_width=*/8});
  auto* expr = MkSysCall(f.arena, "$high", {MkId(f.arena, "a")});
  EXPECT_FALSE(EvalExpr(expr, f.ctx, f.arena).IsKnown());
}

// §20.7: an out-of-range dimension index yields 'x.
TEST(SysTask, DimensionOutOfRangeReturnsUnknown) {
  SysTaskFixture f;
  f.ctx.CreateVariable("x", 8);
  auto* expr =
      MkSysCall(f.arena, "$size", {MkId(f.arena, "x"), MkInt(f.arena, 2)});
  EXPECT_FALSE(EvalExpr(expr, f.ctx, f.arena).IsKnown());
}

// §20.7: for a fixed-size dimension $increment returns 1 when $left >= $right.
// A packed [n-1:0] element dimension has its MSB index on the left, so the
// increment is 1.
TEST(SysTask, PackedIncrementReturnsOne) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$increment", {MkInt(f.arena, 0)});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

// §20.7: for a packed dimension $left is the index of the most significant
// element. A 32-bit integral value is treated as packed [31:0], so $left is 31;
// $high equals $left because $increment is 1, and $size spans the full width.
TEST(SysTask, PackedLeftIsMostSignificantIndex) {
  SysTaskFixture f;
  EXPECT_EQ(
      EvalExpr(MkSysCall(f.arena, "$left", {MkInt(f.arena, 0)}), f.ctx, f.arena)
          .ToUint64(),
      31u);
  EXPECT_EQ(
      EvalExpr(MkSysCall(f.arena, "$high", {MkInt(f.arena, 0)}), f.ctx, f.arena)
          .ToUint64(),
      31u);
  EXPECT_EQ(
      EvalExpr(MkSysCall(f.arena, "$size", {MkInt(f.arena, 0)}), f.ctx, f.arena)
          .ToUint64(),
      32u);
}

// §20.7: for a fixed-size dimension declared in ascending order (e.g. [0:7]),
// $left is the left bound (0) and $right is the right bound (7). Because
// $left < $right, $increment is -1, and $low/$high mirror $left/$right.
TEST(SysTask, FixedSizeAscendingDimensionBounds) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 8;
  info.elem_width = 4;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 4);
  auto q = [&](const char* fn) {
    return static_cast<int32_t>(
        EvalExpr(MkSysCall(f.arena, fn, {MkId(f.arena, "arr")}), f.ctx, f.arena)
            .ToUint64());
  };
  EXPECT_EQ(q("$left"), 0);
  EXPECT_EQ(q("$right"), 7);
  EXPECT_EQ(q("$low"), 0);
  EXPECT_EQ(q("$high"), 7);
  EXPECT_EQ(q("$increment"), -1);
}

// §20.7: $low/$high track $left/$right under the dimension's increment. For a
// queue dimension ($increment == -1) $low equals $left (0) and $high equals
// $right (size-1).
TEST(SysTask, QueueLowReturnsZero) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 2));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 3));
  auto* expr = MkSysCall(f.arena, "$low", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

TEST(SysTask, QueueHighReturnsSizeMinusOne) {
  SysTaskFixture f;
  auto* q = f.ctx.CreateQueue("q", 16, -1);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 1));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 2));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 3));
  auto* expr = MkSysCall(f.arena, "$high", {MkId(f.arena, "q")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
}

// §20.7: dimension 1 is the slowest varying (the unpacked array dimension) and
// the packed element dimension is dimension 2. Selecting dimension 2 queries
// the packed element width.
TEST(SysTask, DimensionTwoSelectsPackedElement) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 8;
  info.elem_width = 4;
  f.ctx.RegisterArray("arr", info);
  f.ctx.CreateVariable("arr", 4);
  auto* dim1 =
      MkSysCall(f.arena, "$size", {MkId(f.arena, "arr"), MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(dim1, f.ctx, f.arena).ToUint64(), 8u);
  auto* dim2 =
      MkSysCall(f.arena, "$size", {MkId(f.arena, "arr"), MkInt(f.arena, 2)});
  EXPECT_EQ(EvalExpr(dim2, f.ctx, f.arena).ToUint64(), 4u);
}

// §20.7: $dimensions returns 0 for a type that is neither an array nor
// equivalent to a simple bit vector. A real is such a type.
TEST(SysTask, DimensionsOfRealReturnsZero) {
  SysTaskFixture f;
  f.ctx.CreateVariable("r", 64);
  f.ctx.RegisterRealVariable("r");
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "r")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

// §20.7: when the first argument would make $dimensions return 0, every other
// query function returns 'x.
TEST(SysTask, QueryOfDimensionlessArgReturnsUnknown) {
  SysTaskFixture f;
  f.ctx.CreateVariable("r", 64);
  f.ctx.RegisterRealVariable("r");
  auto* expr = MkSysCall(f.arena, "$left", {MkId(f.arena, "r")});
  EXPECT_FALSE(EvalExpr(expr, f.ctx, f.arena).IsKnown());
}

// §20.7: the optional dimension index defaults to 1, so a query with no second
// argument reports the slowest-varying (outermost) dimension.
TEST(SysTask, DefaultDimensionIsOne) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 8;
  info.elem_width = 4;
  f.ctx.RegisterArray("m", info);
  f.ctx.CreateVariable("m", 4);
  auto* without_dim = MkSysCall(f.arena, "$size", {MkId(f.arena, "m")});
  auto* with_dim1 =
      MkSysCall(f.arena, "$size", {MkId(f.arena, "m"), MkInt(f.arena, 1)});
  EXPECT_EQ(EvalExpr(without_dim, f.ctx, f.arena).ToUint64(),
            EvalExpr(with_dim1, f.ctx, f.arena).ToUint64());
  EXPECT_EQ(EvalExpr(without_dim, f.ctx, f.arena).ToUint64(), 8u);
}

// §20.7: a string is a nonarray type that is equivalent to a simple bit
// vector, so $dimensions returns 1 even when the string currently holds no
// characters (its bit-vector width does not drive the dimension count).
TEST(SysTask, DimensionsOfStringReturnsOne) {
  SysTaskFixture f;
  f.ctx.CreateVariable("s", 0);
  f.ctx.RegisterStringVariable("s");
  auto* expr = MkSysCall(f.arena, "$dimensions", {MkId(f.arena, "s")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
}

// §20.7: a string has no unpacked dimensions, so $unpacked_dimensions is 0.
TEST(SysTask, UnpackedDimensionsOfStringReturnsZero) {
  SysTaskFixture f;
  f.ctx.CreateVariable("s", 0);
  f.ctx.RegisterStringVariable("s");
  auto* expr = MkSysCall(f.arena, "$unpacked_dimensions", {MkId(f.arena, "s")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

// §20.7: a dynamic array dimension behaves like a queue dimension — $left is 0,
// $increment is -1, and $size/$right reflect the current element count.
TEST(SysTask, DynamicArrayDimension) {
  SysTaskFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 5;
  info.elem_width = 8;
  info.is_dynamic = true;
  f.ctx.RegisterArray("d", info);
  f.ctx.CreateVariable("d", 8);
  EXPECT_EQ(EvalExpr(MkSysCall(f.arena, "$left", {MkId(f.arena, "d")}), f.ctx,
                     f.arena)
                .ToUint64(),
            0u);
  EXPECT_EQ(EvalExpr(MkSysCall(f.arena, "$size", {MkId(f.arena, "d")}), f.ctx,
                     f.arena)
                .ToUint64(),
            5u);
  EXPECT_EQ(EvalExpr(MkSysCall(f.arena, "$right", {MkId(f.arena, "d")}), f.ctx,
                     f.arena)
                .ToUint64(),
            4u);
  EXPECT_EQ(static_cast<int32_t>(
                EvalExpr(MkSysCall(f.arena, "$increment", {MkId(f.arena, "d")}),
                         f.ctx, f.arena)
                    .ToUint64()),
            -1);
}

}  // namespace
