#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
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
  // An index expression with any x or z bit makes the index invalid, just as
  // an out-of-bounds index does; the read of the 4-state array then returns x.
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
  // The size of a part-select is fixed by its constant width operand even when
  // the starting position comes from a runtime variable: the same '+:' select
  // yields a result of the constant width regardless of the variable base.
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

  // A different runtime position selects different bits but the width — the
  // constant size of the part-select — is unchanged.
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
  // Driving an assignment whose index is out of bounds through the statement
  // execution path performs no operation: the in-range element keeps the value
  // it was given and the out-of-bounds element is never materialized.
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
  // An index expression carrying an x or z bit is invalid, so the write must do
  // nothing. In particular it must not fall through to a defined element (an x
  // index can numerically collapse to 0) and overwrite it.
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
  // Table 7-1: reading an unpacked array of a 2-state integral type through an
  // invalid (out-of-bounds) index yields a known '0, whereas a 4-state element
  // type yields x. Here the 2-state-ness that selects the Table 7-1 row is
  // produced by the `byte` declaration rather than hand-set on the array, and
  // the out-of-bounds read is driven through the full pipeline.
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
  // §7.4.5: a slice may apply to one dimension while other dimensions carry
  // single index values. Here the outer dimension is indexed with a single
  // value (A[1]) and the inner dimension is sliced ([0:1]); the result is the
  // two addressed elements concatenated (element 0 in the low bits). The array
  // is built from a real multidimensional declaration and driven end-to-end.
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
  // §7.4.5: the part-select size is a constant expression, which §11.2.1 allows
  // to be a parameter. Complementing the elaborator's acceptance of a parameter
  // width, this drives the resolved width through the runtime part-select: the
  // parameter W selects an 8-bit slice at the runtime position, yielding the
  // same bits a literal 8 would.
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

// §7.4.5 gives an unpacked array the same three slice forms a vector has, and
// its example `int i = bitvec[j +: k];` is the indexed one. The second operand
// of an indexed form is the width, not the far end point, so `arr[2 +: 3]`
// covers the three elements 2, 3 and 4 -- exactly what `arr[2:4]` covers. The
// tests below state that equivalence rather than a bit pattern, because §7.4.5
// also makes the slice of an unpacked array an unpacked array, and an
// equivalence between two spellings of one range holds whichever way the read
// is represented.
//
// A range and a width that coincide would hide the defect these cover: for
// `arr[b +: w]`, reading the operands as two end points happens to give the
// right elements whenever b + w - 1 equals max(b, w). b = 2 with w = 3 is the
// smallest pair where the two readings part company.
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

// §7.4.5: `-:` runs downward to the named position, so `arr[4 -: 3]` covers
// elements 2, 3 and 4 -- the same three, addressed from the other end.
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

// §7.4.5: a slice applies to one dimension while the others carry single index
// values, and the indexed forms are available on that sliced dimension too.
// This is a separate read path from the single-dimension one above, so the
// width reading has to hold on it independently. A base of 2 with a width of 2
// is the discriminating pair for `+:` here: read as end points it addresses the
// single element 2.
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

// §7.4.5: the descending indexed form on a sliced inner dimension. A base of 4
// with a width of 2 is the discriminating pair for `-:`: read as end points it
// addresses three elements starting at 2 rather than the two ending at 4.
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

// §7.4.5: "A slice name of an unpacked array is an unpacked array." The
// clause's own example assigns a two-element slice to a two-element array:
//
//   bit signed [31:0] busA [7:0];   // unpacked array of 8 32-bit vectors
//   int busB [1:0];                 // unpacked array of 2 integers
//   busB = busA[7:6];               // select a 2-vector slice from busA
//
// so the destination holds the two elements the slice names, one each, rather
// than the single value their concatenation would make. Both arrays are
// written ascending here, so this case fixes the count and the values; which
// end of each array a position counts from is what the cases below separate.
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

// §7.4.5: the indexed form names the same unpacked array as the range form
// covering the same run, so it fills the destination the same way. A base of 6
// with a width of 2 discriminates: read as end points it would address five
// elements starting at 2.
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

// §7.4.5: a queue is the other destination that can hold the unpacked array a
// slice names, and the count is what distinguishes an unpacked result from a
// packed one: three elements make a queue of three, not a queue of one holding
// their concatenation.
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

// §7.4.5 with the declarations the clause itself gives its example:
//
//   bit signed [31:0] busA [7:0];
//   int busB [1:0];
//   busB = busA[7:6];
//
// `busA` descends, so the slice's first element is `busA[7]`; `busB` descends
// too, so its first element is `busB[1]`, and the assignment leaves
// `busB[1] == busA[7]`. Reversing both ends of a copy cancels out, so this
// agrees with the ascending spelling above rather than discriminating against
// it -- it holds the clause's own text to its own declarations, and guards the
// direction handling from being applied at one end only.
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

// §7.4.5: "A slice name of an unpacked array is an unpacked array", and one
// unpacked array is assigned to another by position, not by index. A descending
// source names its highest-indexed element first, so that element fills the
// ascending destination's lowest. Pairing by ascending index at both ends would
// instead leave `dst[0] == src[0]`, which is the reverse of this.
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

// §7.4.5, the same rule with the two directions exchanged: an ascending source
// names its lowest-indexed element first, and a descending destination holds
// its first element at its highest index, so `src[0]` lands in `dst[1]`.
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

// §7.4.5: a slice may name the destination as well as the source, which is a
// separate write path from assigning to the array as a whole. The window is cut
// from a descending array, so its first position is its highest index and the
// ascending source's first element lands there.
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

// A right-hand side that is not itself a slice is taken as one packed value and
// split into element-width fields. §7.4.5 reads a slice as the concatenation of
// its elements with the lowest-indexed in the low bits, so the split has to put
// the low field back at the lowest index -- which it must keep doing now that
// the writer places elements by declared position rather than by index. The
// destination descends, so the low field is the writer's last position, not its
// first.
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

// §7.4.5 (printed page 156): "A single element of a packed or unpacked array
// can be selected using an indexed name", stated with `bit [3:0] [7:0] j;` and
// `k = j[2]; // select a single 8-bit element from j`. A module port carries
// packed dimensions the same way a variable or a net does, so an index on a
// port declared with more than one of them names an element and not a bit. The
// select sits inside the instantiated module and the parent reads back what it
// drives, so Lowerer::CreateChildModulePorts in src/simulator/lowerer_child.cpp
// is the path that records the element width. 32'hDEADBEEF tells the two
// readings apart: element 1 is 8'hBE, while bit 1 is 1.
TEST(ArrayIndexingAndSlicing, PortSingleIndexSelectsAPackedElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input bit [3:0][7:0] data, output [7:0] q);\n"
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

// §7.4.5 with the indexed name on the left of the assignment, which is a
// separate write path: `p[1] = 8'hAB` on `output bit [3:0][7:0] p` writes the
// element at index 1, meaning bits 15 through 8. The other bits are the
// two-state default of 0 that Table 6-7 gives a `bit` with no initializer, so
// the connected 32-bit net reads 32'h0000_AB00. A bit-select write would leave
// 32'h0000_0002 instead.
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

// §7.4.5 reaches a net declared with more than one packed dimension in the same
// words, since a net is declared with packed dimensions exactly as a variable
// is. Lowerer::RegisterModuleNets in src/simulator/lowerer_register.cpp has
// recorded the element width for a net all along, and no other case reads it:
// `w[1]` on `wire [3:0][7:0] w` holding 32'hDEADBEEF is 8'hBE rather than the 1
// a bit select would give.
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

}  // namespace
