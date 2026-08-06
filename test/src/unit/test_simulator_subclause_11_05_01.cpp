#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(SelectBoundaryBehavior, PartSelectPartialOOB) {
  SimFixture f;

  MakeVar(f, "ov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ov");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);

  EXPECT_EQ(result.words[0].aval & 0x3u, 0x3u);

  EXPECT_NE(result.words[0].bval & 0xCu, 0u);
}

TEST(SelectBoundaryBehavior, BitSelectOOBReturnsX) {
  SimFixture f;
  MakeVar(f, "bov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bov");
  sel->index = MakeInt(f.arena, 10);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SelectBoundaryBehavior, PartSelectCompletelyOOBReturnsX) {
  SimFixture f;
  MakeVar(f, "cov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "cov");
  sel->index = MakeInt(f.arena, 12);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0xFu);
}

TEST(SelectBoundaryBehavior, TwoStateBitSelectOOBReturnsZero) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("tsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  v->is_4state = false;
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "tsv");
  sel->index = MakeInt(f.arena, 10);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  // A two-state object yields 0 (not x) for an out-of-bounds bit-select.
  EXPECT_EQ(result.words[0].bval & 1u, 0u);
  EXPECT_EQ(result.words[0].aval & 1u, 0u);
}

TEST(SelectXZHandling, TwoStateBitSelectXZIndexReturnsZero) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("tsx", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  v->is_4state = false;
  MakeVar4(f, "tsi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "tsx");
  sel->index = MakeId(f.arena, "tsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  // An unknown index on a two-state object yields 0 (not x).
  EXPECT_EQ(result.words[0].bval & 1u, 0u);
  EXPECT_EQ(result.words[0].aval & 1u, 0u);
}

TEST(SelectXZHandling, BitSelectXAddr) {
  SimFixture f;

  auto* v = f.ctx.CreateVariable("bsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "bsi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bsv");
  sel->index = MakeId(f.arena, "bsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SelectXZHandling, PartSelectXAddr) {
  SimFixture f;

  auto* v = f.ctx.CreateVariable("psv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "psi", 4, 0, 1);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "psv");
  sel->index = MakeId(f.arena, "psi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(ExpressionSim, PartSelectRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[3:0];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectPlus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[0+:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(ExpressionSim, IndexedPartSelectMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[7-:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(ExpressionSim, IndexedPartSelectRuntimeVaryingBase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [3:0] sel;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    sel = 4;\n"
      "    x = data[sel +: 4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  // The base of an indexed part-select is evaluated at run time: sel==4
  // selects bits [7:4] of 0xABCD, which is 0xC.
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, BitSelectOfConcatenation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[6];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  // A concatenation is a valid operand for a bit-select: {a,b} is 8'b1100_0011,
  // and bit 6 (the next-to-top bit, contributed by a) is 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, PartSelectOfConcatenation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    a = 4'b1100;\n"
      "    b = 4'b0011;\n"
      "    x = {a, b}[7:4];\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  // A concatenation is a valid operand for a part-select: bits [7:4] of
  // {a,b} == 8'b1100_0011 select a, which is 4'b1100 (0xC).
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, PackedStructBitSelect) {
  SimFixture f;
  // §11.5.1: a packed structure is a valid bit-select operand. It presents as
  // a single vector (§7.4.1), so bit 0 of {hi=4'hC, lo=4'h3} == 8'hC3 is 1.
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic x;\n"
      "  initial begin s = 8'hC3; x = s[0]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ExpressionSim, PackedStructPartSelect) {
  SimFixture f;
  // §11.5.1: a part-select of a packed structure extracts a contiguous field
  // of its single-vector image; bits [7:4] of 8'hC3 are the high nibble 0xC.
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic [3:0] x;\n"
      "  initial begin s = 8'hC3; x = s[7:4]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCu);
}

TEST(ExpressionSim, ParameterBitAndPartSelect) {
  SimFixture f;
  // §11.5.1: a parameter is among the operands a bit-select or part-select may
  // address (a parameter is a constant operand, §11.2.1). Selecting from a
  // vector parameter reads the addressed bits of its constant value: bit 0 of
  // 16'hABCD is 1, and bits [15:8] are 0xAB.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter [15:0] P = 16'hABCD;\n"
      "  logic pb;\n"
      "  logic [7:0] phi;\n"
      "  initial begin pb = P[0]; phi = P[15:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* pb = f.ctx.FindVariable("pb");
  auto* phi = f.ctx.FindVariable("phi");
  ASSERT_NE(pb, nullptr);
  ASSERT_NE(phi, nullptr);
  EXPECT_EQ(pb->value.ToUint64(), 1u);
  EXPECT_EQ(phi->value.ToUint64(), 0xABu);
}

TEST(PrimarySim, PrimaryBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial begin data = 8'b10101010; x = data[1]; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LvalueSim, VarLvalueBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[3] = 1; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectPlus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[8+:8] = 8'hAB; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

TEST(LvalueSim, VarLvalueIndexedPartSelectMinus) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[15-:8] = 8'hCD; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

// The single-bit result `r` a select left behind after `src` ran.
//
// §11.5.1 gives an invalid address -- an index outside the declared bounds, or
// one carrying x or z bits -- a result that depends on the state of the object
// selected from: x on a 4-state one, 0 on a 2-state one. Each source below
// states one such select and reads the outcome through one of these.
void ExpectSelectOfFourStateReadsX(const char* src) {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

void ExpectSelectOfTwoStateReadsZero(const char* src) {
  SimFixture f;
  auto* var = RunAndFindVar(src, f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
}

// §11.5.1: an out-of-bounds bit-select of a 4-state object yields x. The
// object's 4-state-ness is produced by its `logic` declaration, so this drives
// the rule end-to-end instead of stubbing the state flag.
TEST(ExpressionSim, BitSelectOutOfBoundsFourStateReadsX) {
  ExpectSelectOfFourStateReadsX(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; r = d[10]; end\n"
      "endmodule\n");
}

// §11.5.1: the same out-of-bounds bit-select of a 2-state object (`bit`) yields
// 0, not x -- discriminating against the 4-state case above.
TEST(ExpressionSim, BitSelectOutOfBoundsTwoStateReadsZero) {
  ExpectSelectOfTwoStateReadsZero(
      "module t;\n"
      "  bit [7:0] d;\n"
      "  bit r;\n"
      "  initial begin d = 8'hFF; r = d[10]; end\n"
      "endmodule\n");
}

// §11.5.1: a bit-select whose index has x/z bits is an invalid address; on a
// 4-state object it yields x. The unknown index is produced by a real
// assignment rather than a hand-set flag.
TEST(ExpressionSim, BitSelectUnknownIndexFourStateReadsX) {
  ExpectSelectOfFourStateReadsX(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] i;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; i = 4'bxxxx; r = d[i]; end\n"
      "endmodule\n");
}

// §11.5.1: an unknown index on a 2-state object yields 0, not x.
TEST(ExpressionSim, BitSelectUnknownIndexTwoStateReadsZero) {
  ExpectSelectOfTwoStateReadsZero(
      "module t;\n"
      "  bit [7:0] d;\n"
      "  logic [3:0] i;\n"
      "  bit r;\n"
      "  initial begin d = 8'hFF; i = 4'bxxxx; r = d[i]; end\n"
      "endmodule\n");
}

// §11.5.1: a part-select entirely outside the declared bounds reads as x. d is
// [7:0]; [13:10] is wholly out of range, so all four bits come back x.
TEST(ExpressionSim, PartSelectCompletelyOutOfBoundsReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] r;\n"
      "  initial begin d = 8'hA5; r = d[13:10]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0xFu);
}

// §11.5.1: a partially out-of-range part-select reads x for the out-of-range
// bits and the stored value for the in-range bits. For 8'hA5 (1010_0101),
// d[9:6] gives {x, x, bit7=1, bit6=0}.
TEST(ExpressionSim, PartSelectPartiallyOutOfBoundsReadsXForOutOfRangeBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] r;\n"
      "  initial begin d = 8'hA5; r = d[9:6]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].bval & 0xCu, 0xCu);
  EXPECT_EQ(var->value.words[0].bval & 0x3u, 0u);
  EXPECT_EQ(var->value.words[0].aval & 0x3u, 0x2u);
}

// §11.5.1: writing through an out-of-bounds bit-select has no effect on the
// stored value.
TEST(ExpressionSim, BitSelectOutOfBoundsWriteHasNoEffect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'hAB; d[10] = 1'b1; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §11.5.1: a partially out-of-range part-select write affects only the in-range
// bits. d[9:6] = 4'hF on the [7:0] object sets bits 7 and 6 only.
TEST(ExpressionSim, PartSelectPartiallyOutOfBoundsWriteAffectsInRangeOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin d = 8'h00; d[9:6] = 4'hF; end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC0u);
}

// §11.5.1: a packed array is a valid bit-select operand. The array is built
// from real §7.4.1 packed-array syntax and indexed end-to-end: element pa[1]
// of the [3:0][7:0] array holding 32'h0000_0100 is 8'h01, so bit pa[1][0] is 1.
TEST(ExpressionSim, MultiDimPackedArrayBitSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] pa;\n"
      "  logic b;\n"
      "  initial begin pa = 32'h0000_0100; b = pa[1][0]; end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.5.1: the bounds of a non-indexed part-select are constant expressions; a
// parameter is such a constant (§11.2.1). data[P:0] with P==7 selects [7:0] of
// 16'hA5A5, i.e. 0xA5.
TEST(ExpressionSim, ParameterNonIndexedPartSelectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter integer P = 7;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial begin data = 16'hA5A5; y = data[P:0]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// §11.5.1: a localparam is likewise a constant bound for a non-indexed
// part-select, taking the localparam code path rather than the parameter one.
TEST(ExpressionSim, LocalparamNonIndexedPartSelectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam integer L = 7;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial begin data = 16'hA5A5; y = data[L:0]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// §11.5.1: "The actual bit that is accessed by an address is, in part,
// determined by the declaration of acc" -- the clause makes the point with
// `logic [15:0] acc` beside `logic [2:17] acc`, two sixteen-bit vectors in
// which the same value of an index names a different bit. Every case above
// declares its vector [N:0], where the index and the bit position coincide and
// the rule is invisible. These declare ranges that do not end at zero, and
// ranges that ascend, so that the declaration is doing the work.

// A descending range whose low bound is 1: index 1 is the least significant
// bit, so it reads the 1 of 8'b0000_0001 rather than the 0 above it.
TEST(DeclaredRangeSelect, BitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b0000_0001; r = d[1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// The index below that low bound is out of bounds even though it is a valid bit
// position of a vector of this width, so it reads x rather than a stored bit.
TEST(DeclaredRangeSelect, BitSelectBelowLowBoundReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

// The write side of the same rule, in the form §18.13.1 writes it: the
// thirty-two bits addressed as [32:1] of a [64:1] vector are its low half, so a
// full-width value written there leaves the upper half alone.
TEST(DeclaredRangeSelect, PartSelectWriteLandsAtTheLowEndOfTheRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [64:1] addr;\n"
      "  initial begin addr = 64'd0; addr[32:1] = 32'hFFFF_FFFF; end\n"
      "endmodule\n",
      f, "addr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// An ascending range, the direction the clause's `logic [0:31] b_vect` example
// uses: its first index addresses the most significant bit, so index 0 of a
// [0:7] vector reads the top bit of 8'b1000_0000.
TEST(DeclaredRangeSelect, AscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:7] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b1000_0000; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// An ascending range that also does not start at zero -- the shape of the
// clause's `logic [2:17] acc`. Indices 1 through 4 of a [1:8] vector are its
// top four bits, so 8'hA5 (1010_0101) reads back as 4'hA.
TEST(DeclaredRangeSelect, AscendingRangePartSelectTakesTheLeadingBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] d;\n"
      "  logic [3:0] y;\n"
      "  initial begin d = 8'hA5; y = d[1:4]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// §11.5.1 states the indexed form against both directions at once: `b_vect[0 +:
// 8]` "== b_vect[0 : 7]" for `logic [0:31] b_vect`. The width is counted along
// the declared range, so those are the vector's eight most significant bits.
TEST(DeclaredRangeSelect, IndexedPartSelectCountsAlongAnAscendingRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:31] b_vect;\n"
      "  logic [7:0] y;\n"
      "  initial begin b_vect = 32'hA5000000; y = b_vect[0 +: 8]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

// An element of an unpacked array is a vector declared with the array's element
// type, so it carries that type's range: index 1 of a [1:8] element is its most
// significant bit, reached here through the element rather than through a
// variable named in the source.
TEST(DeclaredRangeSelect, ArrayElementKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] mem [1:2];\n"
      "  logic r;\n"
      "  initial begin mem[1] = 8'b1000_0000; r = mem[1][1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.5.1 makes its point about `logic [15:0] acc` and `logic [2:17] acc`, but
// what it settles is that "the actual bit that is accessed by an address is, in
// part, determined by the declaration" -- and a net is declared with a packed
// dimension in exactly the same way a variable is. So the three cases below are
// the net counterparts of the variable cases above: the low bound of a
// descending range names the least significant bit, the left bound of an
// ascending range names the most significant one, and a part-select is bounded
// by the range as written rather than by [width-1:0].
TEST(DeclaredRangeSelect, NetBitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] w;\n"
      "  wire r;\n"
      "  assign w = 8'b0000_0001;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetAscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] w;\n"
      "  wire r;\n"
      "  assign w = 8'b1000_0000;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetPartSelectIsBoundedByTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [64:1] w;\n"
      "  wire [31:0] r;\n"
      "  assign w = 64'hFFFF_FFFF_0000_0000;\n"
      "  assign r = w[64:33];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// A select the elaborator writes for itself is resolved against the declared
// range like any other, so §11.5.1 reaches the two places that synthesize one.
// Splitting a concatenation continuous-assign lvalue slices the right-hand side
// per element (§11.4.1), and distributing an instance array's port connection
// slices the connected signal per instance (§23.3.3.5). Both used to count bits
// from the least significant end, which names the intended bit only for a
// declaration written [N:0].
TEST(DeclaredRangeSelect, ConcatLvalueSlicesTheRhsInItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(DeclaredRangeSelect, ConcatLvalueSlicesAnAscendingRhsFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "lo");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

// `out` is declared [3:0] so that only the connection being sliced out of a
// declared range is under test: the rightmost instance takes src[1], the least
// significant bit of `src`, and drives out[0], which is the least significant
// bit of a range where an index and a bit offset already coincide.
TEST(DeclaredRangeSelect, InstanceArrayConnectionSlicesInTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [4:1] src;\n"
      "  wire [3:0] out;\n"
      "  assign src = 4'b0110;\n"
      "  leaf u [3:0] (.a(src), .y(out));\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6u);
}

}  // namespace
TEST(SelectBoundaryBehavior, BitSelectOOBWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("bow", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bow");
  sel->index = MakeInt(f.arena, 10);

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 1, 1), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectBoundaryBehavior, PartSelectCompletelyOOBWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pow", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "pow");
  sel->index = MakeInt(f.arena, 12);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectBoundaryBehavior, PartSelectPartialOOBWriteInRangeOnly) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("ppw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ppw");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64() & 0xC0u, 0xC0u);
  EXPECT_EQ(var->value.ToUint64() & 0x3Fu, 0x00u);
}

TEST(SelectXZHandling, BitSelectXZIndexWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("bxw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* idx_var = f.ctx.CreateVariable("bxi", 4);
  idx_var->value = MakeLogic4Vec(f.arena, 4);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bxw");
  sel->index = MakeId(f.arena, "bxi");

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 1, 1), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(SelectXZHandling, PartSelectXZIndexWriteNoEffect) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("pxw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* idx_var = f.ctx.CreateVariable("pxi", 4);
  idx_var->value = MakeLogic4Vec(f.arena, 4);
  idx_var->value.words[0].aval = 0;
  idx_var->value.words[0].bval = 1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "pxw");
  sel->index = MakeId(f.arena, "pxi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}
