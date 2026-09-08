// §11.5.1 Vector bit-select and part-select addressing, over the selects the
// simulator evaluates and the selects it writes through: a bit-select and a
// part-select whose address falls outside the declared bounds, one whose index
// carries x or z bits, the indexed +: and -: forms, and a select of a
// concatenation, of a packed structure, of a multidimensional packed array and
// of a bound given by a parameter or a localparam. The zero-width part-select
// the clause rejects is here too, named by its report.
//
// Each case takes one of two routes. It builds the select as Expr nodes with
// the builders in lib/cpp/test_builders/builders_ast.h and calls EvalExpr from
// src/simulator/evaluation.h or WriteBitSelect from
// src/simulator/statement_assign.h, or it runs a module source through
// RunAndFindVar in lib/cpp/test_fixtures/fixture_simulator.h and reads back the
// variable the select left its answer in.
//
// Every vector here is declared [N:0], where an index and the bit offset it
// reaches are the same number. The other half of the clause -- that "the actual
// bit that is accessed by an address is, in part, determined by the
// declaration", which only a range not ending at zero or a range that ascends
// can show -- is covered in
// test/src/unit/test_simulator_subclause_11_05_01b.cpp.

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
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

// §11.5.1's second indexed form reads `a[1 -: 4]` as the four indices 1, 0, -1
// and -2: the clause gives `a_vect[15 -: 8]` as `a_vect[15 : 8]` for
// `logic [31:0] a_vect`, so the base names the select's most significant end
// and the width descends from it. Only indices 1 and 0 lie inside
// `logic [7:0] a`, and of a write the clause says "Part-selects that are
// partially out of range shall, when read, return x for the bits that are out
// of range and shall, when written, only affect the bits that are in range."
// Which bits of the right-hand value those two receive follows from the select
// being a four-bit vector whose bit 3 is index 1 and whose bit 2 is index 0:
// `a[1]` takes value bit 3 and `a[0]` takes value bit 2, so `4'b1101` puts 1
// on both and `a` reads 8'h03. Taking the value's own least significant bits
// instead -- `2'b01` -- read 8'h01, which is what this pins. `4'b1101`
// discriminates because its high half `2'b11` differs from its low half
// `2'b01`; an all-ones value such as `4'hF` answers 8'h03 either way. `a`
// starts at 8'h00 so that every bit set in the outcome is one this write put
// there.
TEST(ExpressionSim, PartSelectRunningOffLowEndWritesItsOwnHighBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[1 -: 4] = 4'b1101; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
}

// The same sentence where the select runs off both ends at once. `a[9 -: 12]`
// on `logic [7:0] a` addresses the twelve indices 9 down to -2, of which
// "the bits that are in range" are the whole object, indices 7 through 0. The
// select is a twelve-bit vector whose bit k is index k-2, so index 7 takes
// value bit 9 and index 0 takes value bit 2: the eight bits `a` receives are
// the value's bits 9 through 2, its middle, with two bits spare above and two
// below. Of `12'hABC` (1010_1011_1100) those are 1010_1111, so `a` reads
// 8'hAF. Taking the value's least significant eight bits reads 8'hBC. This
// case pins the distance the value is shifted rather than only its direction:
// a shift of one would read 8'h5E and a shift of three 8'h57, so only the two
// indices that fall below zero give 8'hAF.
TEST(ExpressionSim, PartSelectRunningOffBothEndsWritesItsMiddleBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[9 -: 12] = 12'hABC; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAFu);
}

// The companion running off the high end, which the same sentence governs and
// which no fix to the low end may disturb. `a[9:6]` on `logic [7:0] a`
// addresses indices 9, 8, 7 and 6; the two in range are 7 and 6, and they are
// the select's own least significant end, so they take value bits 1 and 0.
// `4'b1101` puts 0 on `a[7]` and 1 on `a[6]`, and `a` reads 8'h40.
// ExpressionSim.PartSelectPartiallyOutOfBoundsWriteAffectsInRangeOnly above
// states this direction already but writes `4'hF`, every bit of which is the
// same bit, so it answers 8'hC0 whichever bits of the value are taken and
// cannot tell a right answer from a wrong one. `4'b1101` can: a fix that
// shifted the value by the two indices running off the *high* end would take
// value bits 3 and 2 and leave 8'hC0 here, and this case is what fails then.
TEST(ExpressionSim, PartSelectRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin a = 8'h00; a[9:6] = 4'b1101; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x40u);
}

// §11.5.1's non-indexed form, `vect[msb_expr:lsb_expr]`, reaching the same four
// indices as the `-:` case above. The clause asks of the two bounds only that
// they be "constant integer expressions", each "evaluated in a self-determined
// context", and that "the first expression shall address a more significant bit
// than the second expression"; on `logic [7:0] a` the more significant end is
// the numerically larger index, so `a[1:-2]` is well formed and names the run
// 1, 0, -1, -2. The clause's own `a_vect[15 -: 8] // == a_vect[15 : 8]` read at
// base 1 and width 4 is `a[1 -: 4] == a[1:-2]`: the two spellings are one
// select and have to answer alike. Indices 1 and 0 are the ones inside `a`, the
// write "shall ... only affect the bits that are in range", and being the
// select's most significant end they take value bits 3 and 2, so `4'b1101`
// leaves `a` at 8'h03.
//
// The second bound is a unary minus over an unsized decimal, which §11.6.1
// gives 32 bits, and it reached the declared range as the unsigned 4294967294.
// That clamps to a window of {lo: 1, width: 7} and writes the value's low seven
// bits into a[7:1], leaving `a` at 8'h1A: a[0], the one bit the clause requires
// this write to reach, untouched, and seven bits the clause forbids it to touch
// changed.
//
// What this asserts is the pairing rather than a second copy of the number.
// ExpressionSim.PartSelectRunningOffLowEndWritesItsOwnHighBits above already
// pins the indexed spelling at 8'h03, so restating 8'h03 for `b` here would say
// nothing that is not already said. The equality is what only this case can
// say, and it is the clause's own; pinning 8'h03 on `a` beside it is what stops
// the pair passing by being wrong together, which an equality alone would
// allow. `4'b1101` discriminates because its high half 2'b11 differs from its
// low half 2'b01 -- `4'hF` answers 8'h03 whichever two of its bits are taken --
// and both objects start at 8'h00 so that every bit set at the end is one a
// write put there.
TEST(ExpressionSim, NonIndexedPartSelectBelowLowBoundWritesInRangeBitsOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'h00; b = 8'h00;\n"
      "    a[1:-2] = 4'b1101; b[1 -: 4] = 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  auto* indexed = f.ctx.FindVariable("b");
  ASSERT_NE(indexed, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
  EXPECT_EQ(indexed->value.ToUint64(), var->value.ToUint64());
}

// The other reading of a bound whose most significant bit is set, which a
// repair of the negative one must not take. §11.5.1 has each bound of a
// non-indexed part-select "evaluated in a self-determined context", and §5.7.1
// leaves a based literal written without an `s` unsigned, so `4'hE` is the
// four-bit unsigned 14 and `4'hB` is 11: `u[4'hE : 4'hB]` is `u[14:11]`, wholly
// inside `logic [15:0] u`, with nothing out of range at all. Bit 3 of the
// select is index 14 and bit 0 is index 11, so `4'b1101` sets u[14], u[13] and
// u[11] and clears u[12], and `u` reads 16'h6800.
//
// Having the top bit set within its own width is the whole of what these two
// bounds share with a negative one, -2 being the 32-bit 0xFFFFFFFE. A
// sign-aware read of a bound must therefore turn on the signedness the value
// carries and not on that bit: a repair that extends from the value's own width
// whenever the bit is set reads these as -2 and -5, and `u[-2:-5]` is a
// part-select "completely out of the address bounds of the vector", which the
// clause says "shall have no effect on the data stored when written" -- `u`
// would still read 16'h0000. Those two answers are what separate taken as
// written from sign-extended. `4'b1101` rather than `4'hF` again: an all-ones
// value reads 16'h7800 and cannot tell u[12] from its neighbours, and 16'h0000
// as the starting value makes every set bit one this write is answerable for.
TEST(ExpressionSim, UnsignedPartSelectBoundKeepsItsTopBitAsMagnitude) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] u;\n"
      "  initial begin u = 16'h0000; u[4'hE : 4'hB] = 4'b1101; end\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6800u);
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

// §11.5.1: the width_expr of an indexed part-select shall be a positive
// constant integer expression, so a zero width is rejected rather than
// silently writing nothing, and the report names §11.5.1.
TEST(SelectBoundaryBehavior, ZeroWidthPartSelectWriteNames11_5_1) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zwp", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x5A);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "zwp");
  sel->index = MakeInt(f.arena, 2);
  sel->index_end = MakeInt(f.arena, 0);
  sel->is_part_select_plus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0x3), f.ctx, f.arena);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 0,
                            "11.5.1"));
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

// The low-end write at WriteBitSelect itself, the one writer the blocking,
// compound, increment, expression and subroutine-body forms of an assignment
// all reach. §11.5.1 makes `plw[1 -: 4]` the indices 1, 0, -1 and -2 and lets
// the write "only affect the bits that are in range", which here are `plw[1]`
// and `plw[0]`; being the select's most significant end, they take the value's
// bits 3 and 2. `4'hD` is 4'b1101, so both take 1 and `plw` reads 8'h03. The
// value's own low two bits are 2'b01 and read 8'h01. `4'hD` is chosen over the
// `4'hF` that SelectBoundaryBehavior.PartSelectPartialOOBWriteInRangeOnly
// writes for exactly that reason: an all-ones value cannot separate the two.
TEST(SelectBoundaryBehavior, PartSelectPartialOOBLowEndSourceBits) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("plw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "plw");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_minus = true;

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xD), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
}

// The negative bound at WriteBitSelect itself, the one writer the blocking,
// compound, increment, expression and subroutine-body forms of an assignment
// all reach, and reached here with neither the elaborator nor the lowerer in
// between. The bound is built as a unary minus over the literal 2 rather than
// as a ready-made negative number, because the shape of that value is what the
// defect turns on: §11.6.1 gives an unsized decimal 32 bits and the negation is
// masked to that width, so what arrives at the range is a signed 32-bit
// 0xFFFFFFFE. Projected instead of read with its sign that is 4294967294, and
// PartSelectStorageBits clamps {1, 4294967294} against the [7:0] range to a
// window of {lo: 1, width: 7}: `nlw` read 8'h1A. With its sign it is -2, which
// the range clamps to its low end at index 0, and §11.5.1 leaves the write to
// "only affect the bits that are in range" -- nlw[1] and nlw[0]. They are the
// select's most significant end and so take value bits 3 and 2; `4'hD` is
// 4'b1101, so both take 1 and `nlw` reads 8'h03. `4'hD` rather than the `4'hF`
// of SelectBoundaryBehavior.PartSelectPartialOOBWriteInRangeOnly for the reason
// given above PartSelectPartialOOBLowEndSourceBits: an all-ones value cannot
// separate the value's own low bits from the bits the in-range indices name.
// The read side of the same select. §11.5.1: a part-select "partially out of
// range shall, when read, return x for the bits that are out of range", and the
// bits that are out of range are the select's own least significant ones --
// index 1 is the more significant end, so indices -1 and -2 are result bits 1
// and 0. Reading the bound through ToUint64 gave the second bound 4294967294,
// which is not merely a wrong window: the width is computed from the pair, so
// the read asked for a vector of 4294967294 bits.
//
// 8'hA5 is 1010_0101, so a[1] is 0 and a[0] is 1 and the two bits that are in
// range read 01. A value whose two low bits were alike could not tell them
// apart from each other.
TEST(SelectBoundaryBehavior,
     NegativeNonIndexedBoundReadsXForItsOutOfRangeBits) {
  SimFixture f;

  MakeVar(f, "nrv", 8, 0xA5);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nrv");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 2));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);

  EXPECT_EQ(result.words[0].bval & 0x3u, 0x3u);

  EXPECT_EQ(result.words[0].bval & 0xCu, 0u);
  EXPECT_EQ(result.words[0].aval & 0xCu, 0x4u);
}

TEST(SelectBoundaryBehavior, NegativeNonIndexedBoundClampsToTheLowEnd) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("nlw", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "nlw");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 2));

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xD), f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0x03u);
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
