#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MkSlice(Arena& arena, std::string_view name, uint64_t hi,
                     uint64_t lo) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* hi_expr = arena.Create<Expr>();
  hi_expr->kind = ExprKind::kIntegerLiteral;
  hi_expr->int_val = hi;
  sel->index = hi_expr;
  auto* lo_expr = arena.Create<Expr>();
  lo_expr->kind = ExprKind::kIntegerLiteral;
  lo_expr->int_val = lo;
  sel->index_end = lo_expr;
  return sel;
}

static Expr* MkPlusPartSelect(Arena& arena, std::string_view name,
                              std::string_view pos_var, uint64_t size) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->is_part_select_plus = true;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* pos = arena.Create<Expr>();
  pos->kind = ExprKind::kIdentifier;
  pos->text = pos_var;
  sel->index = pos;
  auto* width = arena.Create<Expr>();
  width->kind = ExprKind::kIntegerLiteral;
  width->int_val = size;
  sel->index_end = width;
  return sel;
}

namespace {

TEST(ArrayIndexingAndSlicing, OutOfBoundsReturnsX) {
  SimFixture f;

  MakeArray4(f, "arr");

  auto in_result = EvalExpr(MakeSelect(f.arena, "arr", 2), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 30u);
  EXPECT_TRUE(in_result.IsKnown());

  auto oob_result = EvalExpr(MakeSelect(f.arena, "arr", 10), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

TEST(ArrayIndexingAndSlicing, UnknownIndexBitMakesIndexInvalid) {
  SimFixture f;
  MakeArray4(f, "arr");

  auto* idx = f.ctx.CreateVariable("idx", 8);
  idx->value = MakeAllX(f.arena, 8);

  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "arr"), MakeId(f.arena, "idx"));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(ArrayIndexingAndSlicing, IndexedPartSelectSizeIsConstantPositionVaries) {
  SimFixture f;

  auto* vec = f.ctx.CreateVariable("vec", 32);
  vec->value = MakeLogic4VecVal(f.arena, 32, 0xAABBCCDDull);
  auto* pos = f.ctx.CreateVariable("pos", 32);
  pos->value = MakeLogic4VecVal(f.arena, 32, 8);

  auto result =
      EvalExpr(MkPlusPartSelect(f.arena, "vec", "pos", 8), f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 0xCCu);

  pos->value = MakeLogic4VecVal(f.arena, 32, 16);
  auto moved =
      EvalExpr(MkPlusPartSelect(f.arena, "vec", "pos", 8), f.ctx, f.arena);
  EXPECT_EQ(moved.width, 8u);
  EXPECT_EQ(moved.ToUint64(), 0xBBu);
}

TEST(ArrayIndexingAndSlicing, ReadSliceConcat) {
  SimFixture f;
  MakeArray4(f, "arr");

  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);

  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

TEST(ArrayIndexingAndSlicing, ExecutedOutOfBoundsWriteLeavesArrayUnchanged) {
  SimFixture f;
  auto* in_range = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    mem[1] = 8'd20;\n"
      "    mem[7] = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "mem[1]");
  ASSERT_NE(in_range, nullptr);
  EXPECT_EQ(in_range->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("mem[7]"), nullptr);
}

TEST(ArrayIndexingAndSlicing, ExecutedUnknownIndexWriteIsNoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [1:0] idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd10;\n"
      "    mem[1] = 8'd20;\n"
      "    idx = 2'bxx;\n"
      "    mem[idx] = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* e0 = f.ctx.FindVariable("mem[0]");
  auto* e1 = f.ctx.FindVariable("mem[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
}

TEST(ArrayIndexingAndSlicing, SourceTwoStateArrayInvalidReadYieldsZero) {
  SimFixture f;
  auto* res = RunAndFindVar(
      "module t;\n"
      "  byte arr [0:3];\n"
      "  logic [7:0] res;\n"
      "  initial begin\n"
      "    arr[0] = 8'd10;\n"
      "    arr[1] = 8'd20;\n"
      "    res = arr[10];\n"
      "  end\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(res, nullptr);
  EXPECT_TRUE(res->value.IsKnown());
  EXPECT_EQ(res->value.ToUint64(), 0u);
}

TEST(ArrayIndexingAndSlicing, SliceOfOneDimensionOfMultidimArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int A[2][3];\n"
      "  logic [63:0] r;\n"
      "  initial begin\n"
      "    A[1][0] = 10;\n"
      "    A[1][1] = 20;\n"
      "    r = A[1][0:1];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, (static_cast<uint64_t>(20) << 32) | 10u);
}

TEST(ArrayIndexingAndSlicing, PartSelectOnPackedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [63:0] data;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    data = 64'hDEADBEEF_CAFEBABE;\n"
      "    result = data[23:16];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFEu);
}

TEST(ArrayIndexingAndSlicing, IndexedPartSelectPlus) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] result;\n"
      "  int base;\n"
      "  initial begin\n"
      "    vec = 32'hAABBCCDD;\n"
      "    base = 8;\n"
      "    result = vec[base +: 8];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCCu);
}

TEST(ArrayIndexingAndSlicing, IndexedPartSelectWidthFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter W = 8;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] result;\n"
      "  int base;\n"
      "  initial begin\n"
      "    vec = 32'hAABBCCDD;\n"
      "    base = 8;\n"
      "    result = vec[base +: W];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCCu);
}

TEST(ArrayIndexingAndSlicing, IndexedPartSelectMinus) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] result;\n"
      "  int base;\n"
      "  initial begin\n"
      "    vec = 32'hAABBCCDD;\n"
      "    base = 15;\n"
      "    result = vec[base -: 8];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCCu);
}

TEST(ArrayIndexingAndSlicing, IndexedPlusPartSelectCoversItsWidthInElements) {
  const char* src =
      "module t;\n"
      "  logic [7:0] arr [0:7];\n"
      "  logic [23:0] indexed;\n"
      "  logic [23:0] ranged;\n"
      "  initial begin\n"
      "    arr[2] = 8'h30;\n"
      "    arr[3] = 8'h40;\n"
      "    arr[4] = 8'h50;\n"
      "    indexed = arr[2 +: 3];\n"
      "    ranged = arr[2:4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "indexed"), RunAndGet(src, "ranged"));
  EXPECT_EQ(RunAndGet(src, "indexed"), 0x504030u);
}

TEST(ArrayIndexingAndSlicing, IndexedMinusPartSelectCoversItsWidthInElements) {
  const char* src =
      "module t;\n"
      "  logic [7:0] arr [0:7];\n"
      "  logic [23:0] indexed;\n"
      "  logic [23:0] ranged;\n"
      "  initial begin\n"
      "    arr[2] = 8'h30;\n"
      "    arr[3] = 8'h40;\n"
      "    arr[4] = 8'h50;\n"
      "    indexed = arr[4 -: 3];\n"
      "    ranged = arr[2:4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "indexed"), RunAndGet(src, "ranged"));
  EXPECT_EQ(RunAndGet(src, "indexed"), 0x504030u);
}

TEST(ArrayIndexingAndSlicing, IndexedPlusPartSelectOnMultidimCoversItsWidth) {
  const char* src =
      "module t;\n"
      "  int a[2][5];\n"
      "  logic [63:0] indexed;\n"
      "  logic [63:0] ranged;\n"
      "  initial begin\n"
      "    a[1][2] = 32'h30;\n"
      "    a[1][3] = 32'h40;\n"
      "    indexed = a[1][2 +: 2];\n"
      "    ranged = a[1][2:3];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "indexed"), RunAndGet(src, "ranged"));
  EXPECT_EQ(RunAndGet(src, "indexed"), 0x0000004000000030ull);
}

TEST(ArrayIndexingAndSlicing, IndexedMinusPartSelectOnMultidimCoversItsWidth) {
  const char* src =
      "module t;\n"
      "  int a[2][5];\n"
      "  logic [63:0] indexed;\n"
      "  logic [63:0] ranged;\n"
      "  initial begin\n"
      "    a[1][3] = 32'h40;\n"
      "    a[1][4] = 32'h50;\n"
      "    indexed = a[1][4 -: 2];\n"
      "    ranged = a[1][3:4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "indexed"), RunAndGet(src, "ranged"));
  EXPECT_EQ(RunAndGet(src, "indexed"), 0x0000005000000040ull);
}

TEST(ArrayIndexingAndSlicing, SliceAssignedToAnArrayFillsItsElements) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  bit signed [31:0] busA [0:7];\n"
                 "  int busB [0:1];\n"
                 "  initial begin\n"
                 "    busA[6] = 32'h60;\n"
                 "    busA[7] = 32'h70;\n"
                 "    busB = busA[6:7];\n"
                 "  end\n"
                 "endmodule\n",
                 "busB", {0x60u, 0x70u});
}

TEST(ArrayIndexingAndSlicing, IndexedSliceAssignedToAnArrayFillsItsElements) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  bit signed [31:0] busA [0:7];\n"
                 "  int busB [0:1];\n"
                 "  initial begin\n"
                 "    busA[6] = 32'h60;\n"
                 "    busA[7] = 32'h70;\n"
                 "    busB = busA[6 +: 2];\n"
                 "  end\n"
                 "endmodule\n",
                 "busB", {0x60u, 0x70u});
}

TEST(ArrayIndexingAndSlicing, SliceAssignedToAQueueBecomesThatManyElements) {
  SimFixture f;
  ElaborateLowerRun(f,
                    "module t;\n"
                    "  int a[0:7];\n"
                    "  int q[$];\n"
                    "  initial begin\n"
                    "    a[2] = 32'h20;\n"
                    "    a[3] = 32'h30;\n"
                    "    a[4] = 32'h40;\n"
                    "    q = a[2 +: 3];\n"
                    "  end\n"
                    "endmodule\n");
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x30u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0x40u);
}

TEST(ArrayIndexingAndSlicing, ClauseExampleDescendingArraysPairByPosition) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  bit signed [31:0] busA [7:0];\n"
                 "  int busB [1:0];\n"
                 "  initial begin\n"
                 "    busA[6] = 32'h60;\n"
                 "    busA[7] = 32'h70;\n"
                 "    busB = busA[7:6];\n"
                 "  end\n"
                 "endmodule\n",
                 "busB", {0x60u, 0x70u});
}

TEST(ArrayIndexingAndSlicing, DescendingSourceSliceFillsAscendingDestination) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int src [1:0];\n"
                 "  int dst [0:1];\n"
                 "  initial begin\n"
                 "    src[0] = 32'h00;\n"
                 "    src[1] = 32'h11;\n"
                 "    dst = src[1:0];\n"
                 "  end\n"
                 "endmodule\n",
                 "dst", {0x11u, 0x00u});
}

TEST(ArrayIndexingAndSlicing, AscendingSourceSliceFillsDescendingDestination) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int src [0:1];\n"
                 "  int dst [1:0];\n"
                 "  initial begin\n"
                 "    src[0] = 32'hA0;\n"
                 "    src[1] = 32'hB0;\n"
                 "    dst = src[0:1];\n"
                 "  end\n"
                 "endmodule\n",
                 "dst", {0xB0u, 0xA0u});
}

TEST(ArrayIndexingAndSlicing,
     DescendingDestinationWindowTakesSliceInDeclaredOrder) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int src [0:1];\n"
                 "  int dst [1:0];\n"
                 "  initial begin\n"
                 "    src[0] = 32'hA0;\n"
                 "    src[1] = 32'hB0;\n"
                 "    dst[1:0] = src[0:1];\n"
                 "  end\n"
                 "endmodule\n",
                 "dst", {0xB0u, 0xA0u});
}

TEST(ArrayIndexingAndSlicing,
     PackedRhsFillsDescendingWindowLowFieldAtLowIndex) {
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  int dst [1:0];\n"
                 "  initial dst[1:0] = 64'h000000B0_000000A0;\n"
                 "endmodule\n",
                 "dst", {0xA0u, 0xB0u});
}

TEST(ArrayIndexingAndSlicing, PortSingleIndexSelectsAPackedElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input logic [3:0][7:0] data, output [7:0] q);\n"
      "  assign q = data[1];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [31:0] src;\n"
      "  wire [7:0] r;\n"
      "  leaf u (.data(src), .q(r));\n"
      "  initial src = 32'hDEADBEEF;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEu);
}

TEST(ArrayIndexingAndSlicing, PortSingleIndexTargetWritesAPackedElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(output bit [3:0][7:0] p);\n"
      "  initial p[1] = 8'hAB;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [31:0] r;\n"
      "  leaf u (.p(r));\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0000AB00u);
}

TEST(ArrayIndexingAndSlicing, NetSingleIndexSelectsAPackedElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [3:0][7:0] w;\n"
      "  wire [7:0] r;\n"
      "  assign w = 32'hDEADBEEF;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEu);
}

TEST(ArrayIndexingAndSlicing, SliceWindowElementsGetTheirOwnWords) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wave [0:1];\n"
      "  logic [7:0] echo [0:1];\n"
      "  initial begin\n"
      "    wave[0] = 8'b1z0x0011;\n"
      "    wave[1] = 8'h5A;\n"
      "    echo[0:1] = wave[0:1];\n"
      "    echo[0] = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f, "wave[0]");
  ASSERT_NE(source, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* filled = f.ctx.FindVariable("echo[0]");
  auto* paired = f.ctx.FindVariable("echo[1]");
  ASSERT_NE(filled, nullptr);
  ASSERT_NE(paired, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0x93u);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x50u);
  EXPECT_EQ(filled->value.words[0].aval & 0xFFu, 0x00u);
  EXPECT_EQ(filled->value.words[0].bval & 0xFFu, 0x00u);
  EXPECT_EQ(paired->value.words[0].aval & 0xFFu, 0x5Au);
}

TEST(ArrayIndexingAndSlicing, ArrayFilledFromASliceGetsItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] trunk [0:1];\n"
      "  logic [15:0] limb [0:1];\n"
      "  initial begin\n"
      "    trunk[0] = 16'b1x0z000011110101;\n"
      "    trunk[1] = 16'hA53C;\n"
      "    limb = trunk[0:1];\n"
      "    limb[0] = 16'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* held = f.ctx.FindVariable("trunk[0]");
  auto* taken = f.ctx.FindVariable("limb[1]");
  ASSERT_NE(held, nullptr);
  ASSERT_NE(taken, nullptr);
  EXPECT_EQ(held->value.words[0].aval & 0xFFFFu, 0xC0F5u);
  EXPECT_EQ(held->value.words[0].bval & 0xFFFFu, 0x5000u);
  EXPECT_EQ(taken->value.words[0].aval & 0xFFFFu, 0xA53Cu);
  EXPECT_EQ(taken->value.words[0].bval & 0xFFFFu, 0x0000u);
}

TEST(ArrayIndexingAndSlicing, SliceOfA4StateArrayReadsXForAMissingElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [7:0] b [0:1];\n"
      "  int i;\n"
      "  initial begin\n"
      "    a[0] = 8'h11;\n"
      "    a[1] = 8'h22;\n"
      "    i = 1;\n"
      "    b = a[i +: 2];\n"
      "  end\n"
      "endmodule\n",
      f, "b[1]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(ArrayIndexingAndSlicing, SliceOfA2StateArrayReadsZeroForAMissingElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] a [0:1];\n"
      "  bit [7:0] b [0:1];\n"
      "  int i;\n"
      "  initial begin\n"
      "    a[0] = 8'h11;\n"
      "    a[1] = 8'h22;\n"
      "    i = 1;\n"
      "    b = a[i +: 2];\n"
      "  end\n"
      "endmodule\n",
      f, "b[1]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

TEST(ArrayIndexingAndSlicing, PackedSliceReadIsXForAMissingElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [15:0] p;\n"
      "  int i;\n"
      "  initial begin\n"
      "    a[0] = 8'h11;\n"
      "    a[1] = 8'h22;\n"
      "    i = 1;\n"
      "    p = a[i +: 2];\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx00100010");
}

TEST(ArrayIndexingAndSlicing, ArraySliceAsValueKeepsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a [0:1];\n"
      "  logic [15:0] w;\n"
      "  initial begin\n"
      "    a[0] = 8'h5A;\n"
      "    a[1] = 8'bxxxx_zzzz;\n"
      "    w = a[0:1];\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxzzzz01011010");
}

TEST(ArrayIndexingAndSlicing, ArraySliceAsValueKeepsBitsAcrossAWordBoundary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [39:0] a [0:1];\n"
      "  logic [79:0] w;\n"
      "  initial begin\n"
      "    a[0] = 40'hAABBCCDDEE;\n"
      "    a[1] = 40'h1122334455;\n"
      "    w = a[0:1];\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x334455AABBCCDDEEull);
  EXPECT_EQ(var->value.words[1].aval, 0x1122ull);
}

TEST(ArrayIndexingAndSlicing, ArraySliceAsValueOfSixtyFourBitElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] a [0:1];\n"
      "  logic [127:0] w;\n"
      "  initial begin\n"
      "    a[0] = 64'h1122334455667788;\n"
      "    a[1] = 64'h99AABBCCDDEEFF00;\n"
      "    w = a[0:1];\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x1122334455667788ull);
  EXPECT_EQ(var->value.words[1].aval, 0x99AABBCCDDEEFF00ull);
}

TEST(ArrayIndexingAndSlicing, InvalidIndexReadsAStructureMemberByMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit [3:0] n_t;\n"
      "  typedef struct packed { bit p; int q; } p2_t;\n"
      "  typedef struct packed { bit p; logic q; } p4_t;\n"
      "  typedef struct { logic m; byte n; } in_t;\n"
      "  typedef struct { int a = 5; logic b; int c; n_t d; p2_t e;\n"
      "                   in_t g; p4_t h; } s_t;\n"
      "  typedef union { int i; logic [31:0] l; } u_t;\n"
      "  s_t arr [2];\n"
      "  u_t ua [2];\n"
      "  p4_t pa [2];\n"
      "  int k = 7;\n"
      "  logic [31:0] kx = 'x;\n"
      "  initial begin\n"
      "    $display(\"%0d %b %0d %0d %0d %b\", arr[k].a, arr[k].b, arr[k].c,\n"
      "             arr[k].d, arr[k].e, arr[k].h);\n"
      "    $display(\"%0d %b %0d\", arr[kx].a, arr[kx].b, arr[kx].c);\n"
      "    $display(\"%0d %0h %b\", ua[k].i, ua[k].l, pa[k]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 x 0 0 0 xx\n5 x 0\n0 0 xx\n");
}

TEST(ArrayIndexingAndSlicing, InvalidIndexOfVariableSizeArrayReadsAStructure) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; logic [3:0] b; int c = 5; } s_t;\n"
      "  s_t q[$];\n"
      "  s_t d[];\n"
      "  s_t r, rx, rd;\n"
      "  logic [31:0] kx = 'x;\n"
      "  initial begin\n"
      "    q.push_back('{1, 4'h1, 2});\n"
      "    d = new[1];\n"
      "    r = q[3];\n"
      "    rx = q[kx];\n"
      "    rd = d[4];\n"
      "    $display(\"%0d %h %0d\", r.a, r.b, r.c);\n"
      "    $display(\"%0d %h %0d\", rx.a, rx.b, rx.c);\n"
      "    $display(\"%0d %h %0d\", rd.a, rd.b, rd.c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 x 5\n0 x 5\n0 x 5\n");
}

TEST(ArrayIndexingAndSlicing,
     EnumerationAndNonIntegralElementsReadTheirTableValuesAtAnInvalidIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "interface I; endinterface\n"
                "interface class IC; endclass\n"
                "class C; endclass\n"
                "module top;\n"
                "  typedef enum logic [1:0] {LA, LB} le_t;\n"
                "  typedef enum bit [1:0] {BA, BB} be_t;\n"
                "  typedef enum {IA = 5, IB} ie_t;\n"
                "  le_t le [2];\n"
                "  be_t be [2];\n"
                "  ie_t ie [2];\n"
                "  real r [2];\n"
                "  shortreal sr [2];\n"
                "  string s [2];\n"
                "  C c [2];\n"
                "  IC ic [2];\n"
                "  event e [2];\n"
                "  chandle ch [2];\n"
                "  virtual I vi [2];\n"
                "  int da [2][];\n"
                "  int q [2][$];\n"
                "  int aa [2][int];\n"
                "  int i3 = 3;\n"
                "  initial begin\n"
                "    foreach (le[i]) begin\n"
                "      le[i] = LB;\n"
                "      be[i] = BB;\n"
                "      ie[i] = IB;\n"
                "      r[i] = 1.5;\n"
                "      sr[i] = 2.5;\n"
                "      s[i] = \"hi\";\n"
                "      c[i] = new;\n"
                "      da[i] = new[2];\n"
                "      q[i].push_back(1);\n"
                "      aa[i][4] = 1;\n"
                "    end\n"
                "    $display(\"%b %b %0d\", le[i3], be[i3], ie[i3]);\n"
                "    $display(\"%0f %0f \\\"%s\\\"\", r[i3], sr[i3], s[i3]);\n"
                "    $display(\"%0d %0d %0d %0d %0d\", c[i3] == null, ic[i3] "
                "== null,\n"
                "             e[i3] == null, ch[i3] == null, vi[i3] == null);\n"
                "    $display(\"%0d %0d %0d\", da[i3].size(), q[i3].size(), "
                "aa[i3].num());\n"
                "  end\n"
                "endmodule\n",
                f),
            "xx 00 0\n"
            "0.000000 0.000000 \"\"\n"
            "1 1 1 1 1\n"
            "0 0 0\n");
}

TEST(ArrayIndexingAndSlicing,
     ZIndexAndVariableSizeOutOfBoundsReadTheirTableValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int ia [4];\n"
                       "  logic [7:0] la [4];\n"
                       "  int dyn [];\n"
                       "  int qq [$];\n"
                       "  logic [7:0] ldyn [];\n"
                       "  initial begin\n"
                       "    ia = '{1, 2, 3, 4};\n"
                       "    la = '{1, 2, 3, 4};\n"
                       "    $display(\"%0d %h %0d %h\", ia['z], la['z], "
                       "ia[2'b1z], la[2'b1z]);\n"
                       "    dyn = '{7, 8};\n"
                       "    qq = '{7, 8};\n"
                       "    ldyn = '{7, 8};\n"
                       "    $display(\"%0d %0d %0d %0d %h\", dyn[2], qq[2], "
                       "dyn[-1], qq['x], ldyn[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 xx 0 xx\n"
            "0 0 0 0 xx\n");
}

TEST(ArrayIndexingAndSlicing,
     DISABLED_FixedSizeArrayElementReadsAnArrayOfItsElementValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic [3:0] fa [2][3];\n"
                       "  bit [3:0] fb [2][3];\n"
                       "  logic [3:0] t [3];\n"
                       "  bit [3:0] u [3];\n"
                       "  int i3 = 3;\n"
                       "  initial begin\n"
                       "    fa[0] = '{1, 2, 3};\n"
                       "    fb[0] = '{1, 2, 3};\n"
                       "    t = '{4'h5, 4'h5, 4'h5};\n"
                       "    u = '{4'h5, 4'h5, 4'h5};\n"
                       "    t = fa[i3];\n"
                       "    u = fb[i3];\n"
                       "    $display(\"%b %b %b %b %b %b\", t[0], t[1], t[2], "
                       "u[0], u[1], u[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "xxxx xxxx xxxx 0000 0000 0000\n");
}

TEST(ArrayIndexingAndSlicing,
     TwoStateParameterElementAtAnInvalidIndexFoldsToZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter int A [2] = '{1, 2};\n"
                       "  parameter logic [3:0] L [2] = '{4'h1, 4'h2};\n"
                       "  typedef struct { int arr [3]; } s_t;\n"
                       "  parameter s_t P = '{arr: '{1, 2, 3}};\n"
                       "  parameter int M [2][3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
                       "  localparam int a2 = A[2];\n"
                       "  localparam int p3 = P.arr[3];\n"
                       "  localparam int m14 = M[1][4];\n"
                       "  initial $display(\"%0d %0d %0d\", a2, p3, m14);\n"
                       "endmodule\n",
                       f),
            "0 0 0\n");
}

TEST(ArrayIndexingAndSlicing,
     DISABLED_ParameterElementAtAnXIndexOrOfFourStateTypeFoldsToItsTableValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter int A [2] = '{1, 2};\n"
                       "  parameter logic [3:0] L [2] = '{4'h1, 4'h2};\n"
                       "  typedef struct { int arr [3]; } s_t;\n"
                       "  parameter s_t P = '{arr: '{1, 2, 3}};\n"
                       "  parameter int M [2][3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
                       "  localparam int a2 = A[2];\n"
                       "  localparam int ax = A[1'bx];\n"
                       "  localparam logic [3:0] l5 = L[5];\n"
                       "  logic [a2 + 3:0] w;\n"
                       "  initial $display(\"%0d %b %0d\", ax, l5, $bits(w));\n"
                       "endmodule\n",
                       f),
            "0 xxxx 4\n");
}

TEST(ArrayIndexingAndSlicing,
     WritesAtAZIndexAQueueEndANonblockingWriteAndAMemberSelectDoNothing) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  typedef struct packed { logic [3:0] f; logic [3:0] g; } ps_t;\n"
          "  int a [4];\n"
          "  int d [];\n"
          "  int q [$];\n"
          "  ps_t sa [4];\n"
          "  logic [7:0] la [4];\n"
          "  int i10 = 10;\n"
          "  initial begin\n"
          "    a = '{1, 2, 3, 4};\n"
          "    a['z] = 9;\n"
          "    a[2'b1z] = 9;\n"
          "    $display(\"%p\", a);\n"
          "    d = '{1, 2, 3};\n"
          "    d['x] = 9;\n"
          "    d[-1] = 9;\n"
          "    $display(\"%0d %p\", d.size(), d);\n"
          "    q = '{1, 2, 3};\n"
          "    q[$+2] = 9;\n"
          "    q['x] = 9;\n"
          "    $display(\"%0d %p\", q.size(), q);\n"
          "    q[$+1] = 4;\n"
          "    $display(\"%0d %p\", q.size(), q);\n"
          "    la = '{1, 2, 3, 4};\n"
          "    a[10] <= 9;\n"
          "    la[i10] <= 8'hff;\n"
          "    #1 $display(\"%p %p\", a, la);\n"
          "    foreach (sa[i]) sa[i] = 8'h11;\n"
          "    sa[i10].f = 4'hf;\n"
          "    sa[10][3] = 1'b1;\n"
          "    la[i10][3] = 1'b1;\n"
          "    $display(\"%p %p\", sa, la);\n"
          "  end\n"
          "endmodule\n",
          f),
      "'{1, 2, 3, 4}\n"
      "3 '{1, 2, 3}\n"
      "3 '{1, 2, 3}\n"
      "4 '{1, 2, 3, 4}\n"
      "'{1, 2, 3, 4} '{1, 2, 3, 4}\n"
      "'{'{f:1, g:1}, '{f:1, g:1}, '{f:1, g:1}, '{f:1, g:1}} '{1, 2, 3, 4}\n");
}

TEST(ArrayIndexingAndSlicing,
     DISABLED_DynamicArrayWriteOnePastTheEndDoesNothing) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int d [];\n"
                       "  initial begin\n"
                       "    d = '{1, 2, 3};\n"
                       "    d[d.size()] = 9;\n"
                       "    d[5] = 9;\n"
                       "    $display(\"%0d %p\", d.size(), d);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 '{1, 2, 3}\n");
}

}  // namespace
