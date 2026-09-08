#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §11.4.12: bits of a concatenation may be selected as if it were a packed
// array with range [n-1:0]. Driven end-to-end from real source so the select
// operates on a concatenation produced by the parser and elaborator, not a
// hand-built expression. {a,b} with a=4'hA, b=4'h5 is 8'hA5 = 1010_0101, so
// [5:2] extracts 4'h9 and bit [7] (the MSB) is 1.
TEST(ConcatenationSim, PartSelectOnConcatRhsFullPipeline) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [3:0] a, b;\n"
                      "  logic [3:0] result;\n"
                      "  initial begin\n"
                      "    a = 4'hA;\n"
                      "    b = 4'h5;\n"
                      "    result = {a, b}[5:2];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x9u);
}

// A single bit of a concatenation is indexed through the same [n-1:0] packed
// range. {a,b} = 8'hA5 = 1010_0101, so bit [7] (MSB) is 1, bit [0] (LSB) is 1,
// and bit [4] is 0. Driven end-to-end from real source.
TEST(ConcatenationSim, BitSelectOnConcatRhsFullPipeline) {
  const char* src =
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic b7, b0, b4;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    b7 = {a, b}[7];\n"
      "    b0 = {a, b}[0];\n"
      "    b4 = {a, b}[4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b7"), 1u);
  EXPECT_EQ(RunAndGet(src, "b0"), 1u);
  EXPECT_EQ(RunAndGet(src, "b4"), 0u);
}

// §11.4.12: a concatenation is a packed vector usable on the left-hand side of
// an assignment. The LRM's own example uses scalar (1-bit) targets. Assigning
// 3'b101 to {log1, log2, log3} distributes bits MSB-first, so log1=1, log2=0,
// log3=1; reading them back through the same concatenation reconstructs 3'b101.
TEST(ConcatenationSim, LhsConcatDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  logic [2:0] r;\n"
      "  initial begin\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "    r = {log1, log2, log3};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 0b101u);
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

TEST(EvalOp, ConcatXZPropagation) {
  SimFixture f;

  MakeVar4(f, "ca", 4, 0b1001, 0b0101);

  auto* bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ConcatWidthIsSumOfElements) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("a", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* vb = f.ctx.CreateVariable("b", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0xC);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "a"));
  concat->elements.push_back(MakeId(f.arena, "b"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xABCu);
}

// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so §11.4.12's left-hand concatenation is the same
// statement inside a subroutine body as in the initial block above. The
// subroutine body runs on the statement executor in eval_function_body.cpp,
// which named no concatenation form at all, so the assignment wrote nothing and
// reported nothing and every target kept the value it already had. The cases
// below write from a subroutine and read from outside it.

// The LRM's own example, moved into a function body. Each target is read
// separately, since a distribution that put the whole value in one of them
// would still leave the others at 0 and so would be told apart by reading all
// three rather than their concatenation.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  function void put();\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    log1 = 0; log2 = 0; log3 = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

// A task called with parentheses runs its body on the ordinary statement
// executor rather than the subroutine one: SetupTaskCall claims a kTaskDecl
// and ExecInlineTaskCall walks the body through ExecStmt, where a void
// function of the same shape is declined there and reaches ExecFunctionBody.
// So this is the rule read through a task call rather than a second reading of
// the subroutine executor, and the function case above is what claims that.
// §11.6 sizes the sum by the concatenation's width, which is where the
// carry-out lands, so this reads the width and the write together: carry is the
// bit a sixteen-bit sum could not hold.
TEST(ConcatenationSim, LhsConcatInATaskBodyTakesTheCarryOut) {
  const char* src =
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic carry;\n"
      "  logic [15:0] acc;\n"
      "  task add();\n"
      "    {carry, acc} = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    carry = 0; acc = 16'hFFFF;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "carry"), 1u);
  EXPECT_EQ(RunAndGet(src, "acc"), 0u);
}

// §11.4.12's concatenation may contain a concatenation, and the inner one takes
// its slice and distributes it again. A writer that walked the elements flatly
// would hand the inner brace's whole slice to one target or drop it, so b and c
// are what separate the readings.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyReachesANestedConcatenation) {
  const char* src =
      "module t;\n"
      "  logic p, q, r;\n"
      "  function void put();\n"
      "    {p, {q, r}} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    p = 0; q = 0; r = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 1u);
  EXPECT_EQ(RunAndGet(src, "q"), 0u);
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// An element that is a select takes the bits it named and leaves the rest of
// its variable standing. `v` is loaded with 8'hF0 first, so a writer that gave
// the element's slice to the whole variable would read 0x0A where the part
// written alone reads 0xFA.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyWritesOnlyTheBitsASelectNames) {
  const char* src =
      "module t;\n"
      "  logic x;\n"
      "  logic [7:0] v;\n"
      "  function void put();\n"
      "    {x, v[3:0]} = 5'b1_1010;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    v = 8'hF0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "x"), 1u);
  EXPECT_EQ(RunAndGet(src, "v"), 0xFAu);
}

// §4.9.3 puts the obligation on the writer of a blocking assignment: when the
// process is returned it "performs the assignment to the left-hand side and
// enables any events based upon the update of the left-hand side". §9.4.2 says
// which events those are for an event control written `@(a)`: "A non-edge
// implicit event shall be detected on any change in the value of the
// expression." The clause draws no distinction by the statement form that
// produced the change, nor by whether the change touched the whole variable or
// four of its bits, so a concatenation target whose element is a select owes
// the same wake-up as a plain assignment to that select.
//
// UnpackConcatLhs wrote a select element through WriteBitSelect and continued
// straight to the next element. WriteBitSelect notifies nobody -- its three
// other callers each make the notify themselves -- so this arm performed the
// assignment and enabled no event: the counter read 1, the wake at time 1 and
// nothing for the concatenation, where the rule requires 2. This case is the
// select arm of that loop; the whole-variable arm is the case below it.
//
// `a` is loaded with 8'hF0 at time 1 and 12'h9AB puts 4'h9 into a[3:0] at time
// 2, so `a` goes 8'hF0 -> 8'hF9. That is a genuine change, which is what a
// non-edge event requires: writing back the value `a` already held would leave
// nothing for §9.4.2 to detect and the case would claim nothing. Every write to
// `a` sits behind a `#1`, so the count does not turn on whether the always
// block arms before or after the initial block's time-zero statements -- the
// load is the first wake and the concatenation the second either way. Reading
// `a` back as 8'hF9 beside the counter is what stops the case passing because
// the write never landed at all.
TEST(ConcatenationSim, LhsConcatSelectElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] woke;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    woke = 8'd0;\n"
      "    #1 a = 8'hF0;\n"
      "    #1 {a[3:0], b} = 12'h9AB;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a) woke = woke + 1;\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 2u);
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xF9u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xABu);
}

// The same statement reaching the other arm of the same loop. `{a, b} =
// 16'hF9AB` names `a` whole, so UnpackConcatLhs writes `var->value` and calls
// NotifyWatchers two lines below the select arm, and it has always done so:
// this case passed before the fix and reads the same 2 it read then. It leaves
// `a` at the very same 8'hF9 by the very same change from 8'hF0, so the only
// thing separating it from the case above is which arm carried the write.
//
// That is why it is here. It is not a second claim about concatenation targets
// waking event controls -- the case above makes that claim on its own. It is
// what says the two arms of one loop now agree, so that a fix satisfying the
// case above by notifying twice on this arm would have something to answer to.
TEST(ConcatenationSim,
     LhsConcatWholeVariableElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] woke;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    woke = 8'd0;\n"
      "    #1 a = 8'hF0;\n"
      "    #1 {a, b} = 16'hF9AB;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a) woke = woke + 1;\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 2u);
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xF9u);
}

// §11.5.1 gives an out-of-bounds bit-select a value rather than an absence. It
// makes a bit-select the extraction of "a particular bit from a vector", and
// where "the bit-select address is invalid (it is out of bounds or has one or
// more x or z bits), then the value returned by the reference shall be x for
// 4-state and 0 for 2-state values". The same clause says separately of the
// write that it "shall have no effect on the data stored when written". So
// `a[9]` on a [7:0] `a` is one bit of the concatenation whichever bit of `a` it
// fails to address -- §11.6.1's Table 11-21 sizes `{i,...,j}` at L(i)+...+L(j),
// and L(a[9]) is one -- and it is a bit that reaches nothing.
//
// 17'h1AAC3 laid out is 1_1010101_0_11000011, so `c` owns bits [16:9] = 8'hD5,
// `a[9]` is bit [8], and `b` owns bits [7:0] = 8'hC3. UnpackConcatLhs sized the
// element with SelectStorageBits, whose zero means "the select that addresses
// no bit of the object", and read that zero as "this element is not there": the
// `continue` ran before `bit_offset += w`, so `c` took bits [15:8] and read
// 8'hAA. The three sentinels are values no expected value takes, so `a`
// standing at 8'h1A says the write reached nothing rather than that it reached
// the right nothing by accident.
TEST(ConcatenationSim,
     LhsConcatElementWithOutOfBoundsBitSelectStillReservesItsBit) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[9], b} = 17'h1AAC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x1Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

// The same defect reached through a part-select, which is what separates "a
// select element reserves one bit" from "a select element reserves the width
// its indices name". §11.5.1 has a part-select address "several contiguous
// bits", and of the wholly out-of-range one it says only that it "shall yield
// the value x when read and shall have no effect on the data stored when
// written" -- nothing there narrows the bits the indices name -- so `a[11:9]`
// is three bits of the nineteen and none of them reaches `a`.
//
// 19'h6ABC3 is 11010101_011_11000011: `c` owns bits [18:11] = 8'hD5, `a[11:9]`
// bits [10:8], and `b` bits [7:0] = 8'hC3. Reserving nothing for the element
// read 8'hAB into `c`. Reserving one bit -- which a fix that answered the
// bit-select width for every select would do -- reads 8'h55. Only the width the
// indices name reads 8'hD5, which is why this case stands beside the one above
// rather than repeating it.
TEST(ConcatenationSim,
     LhsConcatWhollyOutOfBoundsPartSelectReservesTheWidthItsIndicesName) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[11:9], b} = 19'h6ABC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x1Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

// §11.5.1 gives the partially out-of-range part-select its own rule, and not
// the one it gives the wholly out-of-range one: such a select "shall, when
// read, return x for the bits that are out of range and shall, when written,
// only affect the bits that are in range". Which of its bits land says nothing
// about how wide the element is, since §11.6.1 sizes an element from the
// expression, so `a[9:6]` is four bits of the twenty and two of them reach `a`.
//
// 20'hD5AC3 is 11010101_1010_11000011: `c` owns bits [19:12] = 8'hD5, `a[9:6]`
// takes bits [11:8] = 4'b1010, and `b` bits [7:0] = 8'hC3. Of those four bits
// a[9] and a[8] address nothing and a[7:6] takes 2'b10, so `a` goes 8'h1A ->
// 8'h9A; that write is established outside a concatenation by
// ExpressionSim.PartSelectPartiallyOutOfBoundsWriteAffectsInRangeOnly. The
// slice is chosen so its top half and its bottom half read alike, which keeps
// the case a claim about the width the element reserves rather than a claim
// about which bits of the slice the clipped window takes -- no case in test/
// settles that, since the established one writes 4'hF. `c` read 8'h5A before,
// and reads 8'h56 under a fix that reserved the two bits that land instead of
// the four the indices name.
TEST(ConcatenationSim,
     LhsConcatPartiallyOutOfBoundsPartSelectWritesOnlyItsInRangeBits) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[9:6], b} = 20'hD5AC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x9Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

// The in-bounds companion, and the element the ordinary case stands to lose.
// §7.4.1 makes one index of a packed multidimensional array address an element
// rather than a bit, which §11.5.1 states as "the actual bit that is accessed
// by an address is, in part, determined by the declaration": `pa[1]` on a
// [3:0][7:0] `pa` is eight bits and not one. A fix that answered §11.5.1's
// bit-select width -- one -- for every select carrying no second index would
// draw this concatenation's boundaries seven bits out and read 8'hBF into `c`,
// and would satisfy the three cases above while doing it. This case passes
// before the fix and reads the same values after it, so it is what says the
// fix left the in-bounds select where it was.
//
// 24'hD57EC3: `c` owns bits [23:16] = 8'hD5, `pa[1]` bits [15:8] = 8'h7E, and
// `b` bits [7:0] = 8'hC3. `pa` is read whole rather than through `pa[1]`, so a
// slice written to the wrong element of the array is told from one written to
// the right element instead of vanishing into the read.
TEST(ConcatenationSim, LhsConcatPackedArrayElementReservesItsElementWidth) {
  const char* src =
      "module t;\n"
      "  logic [3:0][7:0] pa;\n"
      "  logic [7:0] b, c;\n"
      "  initial begin\n"
      "    pa = 32'h11223344;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, pa[1], b} = 24'hD57EC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "pa"), 0x11227E44u);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

// §11.5.1 requires an indexed part-select's width expression to "be a positive
// constant", so a width of zero names no bit of the object: `a[3 +: 0]` is not
// a narrow select, it is no select at all. §11.6.1's Table 11-21 sizes
// `{i,...,j}` at L(i)+...+L(j), and an element naming no bit adds nothing to
// that sum, so the elements above it sit where they would sit if it were not
// written.
//
// Two functions answer that one question and disagreed. SelectStorageBits
// returns an empty window for the zero declared width, so
// ConcatLhsElemHasWritableBits says the element writes nothing; SelectExprWidth
// measured only the pair PartSelectTargetIndices answers -- 3 and 3 + 0 - 1 = 2
// -- so ConcatLhsElemWidth sized the element at the two bits a[3:2] spans. The
// element claimed two bits of the right-hand value and wrote none of them, and
// every bit of the concatenation above it was displaced by two.
//
// The width has to be unresolvable before the run for the simulator to be what
// answers: written as a literal or a localparam, the elaborator folds it and
// CheckIndexedPartSelectWidthNode rejects it there. A variable `w` holding 0 is
// reported there too -- as the non-constant width it is, §11.5.1 -- but that
// report does not stop the elaboration and the design still lowers and runs,
// which is why the run is read through RunAndFindVar and not RunAndGet, whose
// EXPECT_FALSE(f.has_errors) requires a clean elaboration. Whether the
// simulator owes a §11.5.1 report of its own for the zero it now sees is a
// separate question this case does not ask; it asks only where the bits go.
//
// 18'h2D5C3 is 10_11010101_11000011. `c` owns the concatenation's top eight
// bits and `b` its bottom eight, and the element between them owns none, so a
// sixteen-bit concatenation receives an eighteen-bit value: §10.7 truncates the
// two most significant bits away, leaving `c` bits [15:8] = 8'hD5 and `b` bits
// [7:0] = 8'hC3. Claiming two bits made the concatenation eighteen wide
// instead, and `c` took bits [17:10] and read 8'hB5.
//
// `b` reads 8'hC3 in both readings, and that is why the case is written with a
// `c` above the zero-width element rather than as `{a[3 +: w], b}`:
// UnpackConcatLhs counts its offsets up from the least significant bit and
// §10.7 truncates from the most significant end, so nothing moves an element by
// what stands to its left, and that shorter concatenation would read the same
// 8'hAC out of 10'h3AC either way and claim nothing. `a` standing at its 8'h1A
// sentinel is the other half of the rule -- the element wrote nothing -- and it
// holds in both readings too, SelectStorageBits having always given this
// element an empty window; it is here so that a fix moving the boundary by
// giving the element bits of `a` to write would have something to answer to.
TEST(ConcatenationSim, LhsConcatZeroWidthPartSelectElementClaimsNoBits) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    w = 4'd0;\n"
      "    {c, a[3 +: w], b} = 18'h2D5C3;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x1Au);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0xD5u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xC3u);
}

}  // namespace
