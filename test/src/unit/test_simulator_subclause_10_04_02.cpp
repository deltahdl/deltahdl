
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_nonblocking_swap.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NonblockingAssignSim, OrderingPreservedAcrossInitials) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'd99;\n"
      "    #8 a <= #8 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #12 a <= #4 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0u);
}

TEST(NonblockingAssignSim, BlockingEventsFromNbaProcessedAfter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic q;\n"
      "  logic post_q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    q = 0;\n"
      "    post_q = 0;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) q <= 1;\n"
      "  always @(q) post_q = q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("q")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("post_q")->value.ToUint64(), 1u);
}

TEST(NonblockingAssignSim, ProceduralFlowNotBlockedBySubsequent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] tgt;\n"
      "  logic [7:0] sample;\n"
      "  initial begin\n"
      "    tgt = 8'd5;\n"
      "    tgt <= 8'd99;\n"
      "    sample = tgt;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sample")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("tgt")->value.ToUint64(), 99u);
}

TEST(NonblockingAssignSim, LhsRequiringEvaluationBindsAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    arr[0] = 8'd0;\n"
      "    arr[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    arr[idx] <= 8'hAA;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0u);
}

// §10.4.2 Example 3 / two-step rule: a nonblocking assignment evaluates in two
// steps -- every right-hand side in the time step is sampled before any
// left-hand side is updated. Two NBAs that read each other's variables
// therefore exchange values: each RHS observes the pre-update value. A naive
// sequential (blocking-style) execution would instead leave both variables
// holding b's original value, so a genuine swap rules that misreading out.
TEST(NonblockingAssignSim, SwapExchangesValuesInTwoSteps) {
  SimFixture f;
  ExpectNonblockingPairExchangesValues(f);
}

// §10.4.2 Example 7: intra-assignment-delayed nonblocking assignments in a loop
// make assignments to the same variable "without cancelling previous
// assignments". The loop runs entirely at time 0, scheduling six updates of
// i[0] = 0,1,0,1,0,1 at times 0,10,20,30,40,50. Each scheduled update must
// carry its own sampled value and fire at its own time -- a single shared
// pending slot would let the last-scheduled value win everywhere and drop the
// intervening updates. A second block strobes r1 mid-window to observe the
// distinct values as they take effect.
TEST(NonblockingAssignSim, DelayedNbasToSameVarDoNotCancelEachOther) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  logic r1;\n"
                                   "  logic [2:0] i;\n"
                                   "  logic s0, s1, s2, s3;\n"
                                   "  initial begin\n"
                                   "    for (i = 0; i <= 5; i = i + 1)\n"
                                   "      r1 <= #(i * 10) i[0];\n"
                                   "  end\n"
                                   "  initial begin\n"
                                   "    #5  s0 = r1;\n"
                                   "    #10 s1 = r1;\n"
                                   "    #10 s2 = r1;\n"
                                   "    #10 s3 = r1;\n"
                                   "  end\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("s0")->value.ToUint64(), 0u);  // t=5,  update@0
  EXPECT_EQ(f.ctx.FindVariable("s1")->value.ToUint64(), 1u);  // t=15, update@10
  EXPECT_EQ(f.ctx.FindVariable("s2")->value.ToUint64(), 0u);  // t=25, update@20
  EXPECT_EQ(f.ctx.FindVariable("s3")->value.ToUint64(), 1u);  // t=35, update@30
}

// §10.4.2 gives the nonblocking form the same target the blocking form takes:
// "In this syntax, variable_lvalue is a data type that is valid for a
// procedural assignment statement", and §11.4.12 makes a concatenation one of
// those -- "The concatenation is treated as a packed vector of bits. It can be
// used on the left-hand side of an assignment". So `{a, b} <= 16'h1234` has to
// distribute across a and b exactly as `{a, b} = 16'h1234` does, a taking the
// high byte and b the low one. It did not: ScheduleNonblockingAssign carried an
// arm for a streaming concatenation and none for a plain one, and
// ResolveLhsVariable answers null for a concatenation, so the statement fell
// out of the bottom of the function having scheduled no write and reported no
// diagnostic. This is the IsConcatLhs gate and the ScheduleConcatNba arm behind
// it. Both variables are pre-loaded with sentinels that neither expected value
// can be, because a target left holding its old value is what the defect
// produced; starting them at zero would let "scheduled nothing at all" pass as
// "assigned zero".
TEST(NonblockingAssignSim, ConcatenationTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'h5A;\n"
      "    {a, b} <= 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x12u}, {"b", 0x34u}});
}

// §10.4.2: a nonblocking assignment "evaluates the right-hand side expression,
// schedules the assignment ... to occur at the end of the current time step",
// so the statement after it still reads what the target held before. A
// concatenation target is under the same rule, since the clause distinguishes
// its left-hand sides only by what a procedural assignment accepts. Reading a
// into sample on the very next statement therefore has to answer the old byte
// while a ends the time step holding the new one. This is what the deferral in
// ScheduleConcatNba claims: the unpacker runs from inside an update-region
// callback, not where the statement executed. Doing the distribution eagerly at
// schedule time would leave sample holding 0x12.
TEST(NonblockingAssignSim, ConcatenationTargetIsWrittenInTheNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] sample;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = 8'd6;\n"
      "    {a, b} <= 16'h1234;\n"
      "    sample = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"sample", 5u}, {"a", 0x12u}, {"b", 0x34u}});
}

// §10.9 gives a positional assignment pattern the same standing on the left of
// an assignment that §11.4.12 gives a concatenation, and §10.4.2 asks only that
// the target be one a procedural assignment accepts, so `'{a, b} <= 16'h5678`
// distributes where `'{a, b} = 16'h5678` does. The bare-pattern spelling
// reaches the new arm through IsConcatLhs's kAssignmentPattern case rather than
// its kConcatenation one, and before the fix it too scheduled nothing and
// reported nothing. The elaboration is required to be clean as well as
// non-null: §10.9 rules on a left-hand pattern's notation and bit count, and a
// case that only read the values back could not tell a source the elaborator
// accepted from one it rejected. Sentinels again, for the reason
// ConcatenationTargetDistributesToItsElements gives.
TEST(NonblockingAssignSim, AssignmentPatternTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hC3;\n"
      "    b = 8'h3C;\n"
      "    '{a, b} <= 16'h5678;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"a", 0x56u}, {"b", 0x78u}});
}

// §10.9's pattern carries a data type here, and §10.4.2 does not care which of
// the two spellings names the target, so `pair_t'{a, b} <= 16'hBEEF` has to
// distribute as the bare pattern above does. The typed form arrives as a cast
// whose operand is the pattern, which is the third route into the new arm:
// IsConcatLhs looks through the cast, where ResolveLhsVariable answers null for
// it, so without that unwrapping the statement would again schedule no write
// and raise no diagnostic. The wrong answer this case rules out is the one that
// distinguishes the spellings -- a fix reading only kConcatenation and
// kAssignmentPattern would leave every typed pattern silently dropped.
TEST(NonblockingAssignSim,
     TypedAssignmentPatternTargetDistributesToItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "    pair_t'{a, b} <= 16'hBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"a", 0xBEu}, {"b", 0xEFu}});
}

// §11.4.1 gives a select element of a concatenation target the bits its own
// indices name and no others, so `{a[3:0], b} <= 12'h9AB` writes the low nibble
// of a and leaves the high nibble standing: a ends at 0xF9, not 0x09. This is
// the case that pins the design of the new arm rather than merely its
// existence. Resolving the elements where the statement executes and scheduling
// a whole-variable write for each would answer 0x09, because ResolveLhsVariable
// on a select hands back the whole of the variable selected from -- the
// boundary error ConcatLhsElemWidth records having already been made once on
// the blocking side. Deferring the blocking unpacker instead keeps
// WriteBitSelect as the writer, so the window is the one the element named.
TEST(NonblockingAssignSim, ConcatenationTargetWritesOnlyTheBitsASelectNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'hFF;\n"
      "    {a[3:0], b} <= 12'h9AB;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xF9u}, {"b", 0xABu}});
}

// §9.4.2 makes `@(a)` an implicit event on the expression a -- "The execution
// of a procedural statement can be synchronized with a value change of an
// expression, known as an implicit event" -- and settles what such an event
// answers to: "A non-edge implicit event shall be detected on any change in
// the value of the expression." The clause draws no distinction by which
// statement form produced the change, nor by whether the change touched the
// whole variable or four of its bits. §4.9.4 says where a nonblocking
// assignment makes that change: it "schedules the update as an NBA update
// event ... in the current time step", so the write is performed from
// ScheduleConcatNba's deferred callback rather than where the statement
// executed. That callback is the third route into UnpackConcatLhs, beside the
// blocking statement and the subroutine body, and it is the route this case
// claims. All three inherited one omission: the select-element arm wrote
// through WriteBitSelect and continued to the next element without notifying
// the variable's watchers, though the whole-variable arm two lines below it
// notified, so a took its new value in the update region and nothing waiting
// on a ever ran.
//
// The observation is a count rather than a flag because the count says which
// of two failures happened. a is written twice, once by an ordinary
// whole-variable blocking assignment and once by the concatenation, so a run
// that leaves wakes at 2 detected both changes, one at 1 has a working
// watcher the concatenation's update did not reach -- the defect -- and one at
// 0 has no watcher at all and is not evidence about this arm. Neither write of
// a happens at time 0, so the count does not turn on whether an always block
// arms before or after an initial block's first statement. a and b are
// asserted beside it because a case that only counted wakes could be satisfied
// by an implementation that stopped performing the write: a ends at 0x56, the
// high nibble §11.4.1 leaves alone still standing, and b at 0xC7.
TEST(NonblockingAssignSim,
     ConcatenationTargetSelectElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int wakes;\n"
      "  initial begin\n"
      "    wakes = 0;\n"
      "    #1 a = 8'h50;\n"
      "    b = 8'h0F;\n"
      "    #1 {a[3:0], b} <= 12'h6C7;\n"
      "  end\n"
      "  always @(a) wakes = wakes + 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"wakes", 2u}, {"a", 0x56u}, {"b", 0xC7u}});
}

// §11.5.1 rules on a part-select that hangs off the end of the object it
// selects from: "Part-selects that are partially out of range shall, when
// read, return x for the bits that are out of range and shall, when written,
// only affect the bits that are in range." The clause asks of the two bounds
// of a non-indexed part-select only that they be "constant integer
// expressions", each "evaluated in a self-determined context", and §5.7.1
// leaves an unsized decimal signed, so the `-2` in `a[1:-2]` is the negative 2
// and the select names indices 1, 0, -1 and -2. Only 1 and 0 lie inside
// `logic [7:0] a`; being the select's most significant end they take the
// value's bits 3 and 2, so `4'b1101` leaves `a` at 8'h03.
//
// §10.4.2 asks of a nonblocking target only that "variable_lvalue is a data
// type that is valid for a procedural assignment statement", which is the
// left-hand side §10.4.1 gives the blocking form -- whose own examples include
// `rega[3:5] = 7; // a part-select`. What §10.4 separates the two statements by
// is procedural flow, "different procedural flows in sequential blocks", and
// not which bits a select names. So `b` takes the same write in the blocking
// form beside `a` and the two are asserted equal: the equality is the thing
// only this case can say, and pinning 8'h03 on `a` beside it is what stops the
// pair passing by being wrong together.
// ExpressionSim.NonIndexedPartSelectBelowLowBoundWritesInRangeBitsOnly in
// test_simulator_subclause_11_05_01a.cpp holds the blocking side of this line
// on its own.
//
// The nonblocking path computed the window itself rather than asking the shared
// helper, and read each bound through a uint32_t, so -2 arrived as the
// unsigned 4294967294. The min/max of the two bounds is then {lo: 1, w:
// 4294967294}, which clamps to a width of seven and writes the value's low
// seven bits into a[7:1]: `a` read 8'h1A, with a[0] -- the one bit the clause
// requires this write to reach -- untouched, and seven bits the clause forbids
// it to touch changed. `4'b1101` is what discriminates, its high half 2'b11
// differing from its low half 2'b01; an all-ones value answers 8'h03 whichever
// two of its bits are taken. Both objects start at 8'h00 so that every bit set
// at the end is one a write put there.
TEST(NonblockingAssignSim,
     SelectTargetWithANegativeBoundWritesInRangeBitsOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    b = 8'h00;\n"
      "    a[1:-2] <= 4'b1101;\n"
      "    b[1:-2] = 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}, {"b", 0x03u}});
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64());
}

// The indexed spelling of that same select, which §11.5.1 makes one select with
// it: the clause's own example reads `a_vect[15 -: 8] // == a_vect[15 : 8]`,
// the `-:` form selecting "starting at the base and descending the bit range",
// so at base 1 and width 4 `a[1 -: 4]` is `a[1:-2]`. Indices 1 and 0 are again
// the ones in range and again the select's most significant end, so `4'b1101`
// leaves `a` at 8'h03 here too.
//
// This is the source-offset half of the defect and the half a repair of the
// bound's sign alone would leave standing. ResolvePartSelectNbaRange folded a
// `-:` select running off the bottom to `lo = 0` while keeping the full width
// of four, which puts the value's bit 0 on a[0] and its bit 1 on a[1] instead
// of its bits 2 and 3: `a` read 8'h0D. Nothing about that answer involves a
// negative bound, so the sign fix does not reach it.
TEST(NonblockingAssignSim, SelectTargetRunningOffLowEndWritesItsOwnHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[1 -: 4] <= 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}});
}

// §11.5.1: "The actual bit that is accessed by an address is, in part,
// determined by the declaration of acc", the clause putting `logic [15:0] acc;`
// and `logic [2:17] acc;` side by side to show one index reaching a different
// bit under each. On `logic [15:8] a` the indices 9 and 8 are the object's two
// least significant bits, wholly in range, so `a[9:8] <= 2'b11` leaves `a` at
// 8'h03.
//
// This is the case that separates "the window is computed wrongly" from "the
// declaration is never consulted at all". The nonblocking path took each index
// as an offset from bit 0 and tested it against the width alone, never
// subtracting the declared range's low bound: lo = 8 against a width of 8 reads
// as entirely out of range, ResolvePartSelectNbaRange answered nullopt, and the
// assignment was dropped whole with no diagnostic -- `a` read 8'h00. A fix
// carrying only the bound's sign and the source offset across would still
// answer 8'h00 here. `a` starts at 8'h00 for the reason the cases above give,
// which is also why the failing answer and the starting value coincide: what
// the case observes is that the two bits the clause names were reached.
TEST(NonblockingAssignSim,
     SelectTargetResolvesItsIndicesAgainstTheDeclaredRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:8] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[9:8] <= 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x03u}});
}

// The companion overhanging the top, which the same sentence of §11.5.1
// governs and which no repair of the low end may disturb. `a[9:6]` on
// `logic [7:0] a` names indices 9, 8, 7 and 6; the two in range are 7 and 6,
// and they are the select's own least significant end, so they take the value's
// bits 1 and 0. `4'b1101` puts 0 on a[7] and 1 on a[6], and `a` reads 8'h40.
//
// This passes today and is here to catch the correction applied in the wrong
// direction: a fix that shifted the value by the count of indices running off
// the *high* end rather than the low would take the value's bits 3 and 2 here
// and read 8'hC0. `4'hF` cannot say that, every bit of it being the same bit;
// `4'b1101` can. ExpressionSim.PartSelectRunningOffHighEndStillTakesItsLowBits
// in test_simulator_subclause_11_05_01a.cpp holds this line for the procedural
// writer, and ContAssignStatementSim.SelectTargetRunningOffHighEndStillTakes-
// ItsLowBits holds it for a continuous assignment's driver; the nonblocking
// form reaches the variable through a deferred update callback of its own and
// needs a case of its own.
TEST(NonblockingAssignSim, SelectTargetRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[9:6] <= 4'b1101;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0x40u}});
}

// §10.4.2: the left-hand side of a nonblocking assignment names the variable
// "to which the value is assigned", and a compound select names one element of
// a multidimensional unpacked array -- an element §7.4.2 gives storage of its
// own, which CreateMultiDimLeaves registers under the name "A[1][2]". Reaching
// that element through two index expressions rather than one changes nothing
// about which object the update region writes.
//
// The nonblocking path resolved its target with a single-level element lookup
// that declines when the select's base is itself a select, then fell back to
// the bare name A: the update landed on the array's base variable as a
// bit-select of index 2, and the element itself stayed 0. The blocking form
// A[1][2] = 43 already writes the element, which is what left the two-level
// nonblocking form looking covered by
// NonblockingAssignSim.LhsRequiringEvaluationBindsAtScheduleTime above -- that
// case indexes one dimension, the level the declined lookup does handle.
//
// The #1 is required rather than decorative: a nonblocking assignment takes
// effect in the update region, so a run that ends at time 0 reads the element's
// old value whichever variable the target resolved to.
TEST(NonblockingAssignSim, MultidimElementTargetWritesTheElement) {
  SimFixture f;
  auto* elem = RunAndFindVar(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[1][2] <= 43;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "A[1][2]");
  ASSERT_NE(elem, nullptr);
  EXPECT_EQ(elem->value.ToUint64(), 43u);
}

// The half of the same defect that names it: what the misresolved assignment
// did instead. Falling back to the bare name turned each element target into a
// bit-select of the array's 32-bit base variable -- the variable no element is
// stored in -- so A read 6, bits 2 and 1 set by numbers that were element
// indices, while both elements stayed 0.
//
// Two assignments in one time step, to elements of different rows, hold the
// outer index as well as the inner: a resolution that honoured only the
// innermost select would put both values in the same row. 43 and 5 are odd on
// purpose. The bit-select the defect performs reduces its right-hand side to
// rhs_val.ToUint64() & 1, so an even value would write a 0 bit and leave the
// base variable reading 0 -- the expectation on A would then hold today, for a
// reason that has nothing to do with the element being written.
TEST(NonblockingAssignSim, MultidimElementTargetLeavesTheArrayBaseAlone) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[1][2] <= 43;\n"
      "    A[0][1] <= 5;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"A", 0u}, {"A[1][2]", 43u}, {"A[0][1]", 5u}});
}

// §10.4.2 gives the nonblocking form the target the blocking form takes --
// "variable_lvalue is a data type that is valid for a procedural assignment
// statement" -- and A.8.5 makes a dotted path onto a class property the first
// production of variable_lvalue. §8.3 keeps that property in the object the
// handle designates rather than in any variable of the module, which is the
// whole of what went wrong here: ResolveLhsVariable rebuilt the name "h.f" and
// asked ctx.FindVariable, the variable table holds no such key because the
// property is a member of ClassObject, and ScheduleNonblockingAssign returned
// on the null before acquiring an update event -- no write, no event and no
// diagnostic. The blocking form reaches the property through AssignToScalarLhs,
// which falls back to the struct-field writer for a member access, so the two
// forms disagreed about whether the statement happened at all.
//
// The blocking `h.f = 8'h11` standing in front of the nonblocking write is what
// lets the case name the failure rather than merely notice one. A property
// never written would read 0 both when the scheduled write was dropped and when
// no write reached the object at all; starting it at 8'h11 separates those, an
// answer of 8'h11 saying the object is there and holding what the blocking form
// put in it. The #1 lets the update region run before `r` samples the property.
TEST(NonblockingAssignSim, ClassPropertyTargetReceivesTheScheduledWrite) {
  SimFixture f;
  auto* sampled = RunAndFindVar(
      "class C;\n"
      "  logic [7:0] f;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f = 8'h11;\n"
      "    h.f <= 8'hA5;\n"
      "    #1 r = h.f;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 0xA5u);
}

// The same sentence of §10.4.2 settles when the handle in that path is read: a
// "class handle" in the left-hand side "shall be evaluated at the same time as
// the expression on the right-hand side", which is where the statement
// executes and not where the update region runs. So `h.f <= 8'hA5` followed by
// `h = other` in the same time step writes the object h designated when the
// statement ran, and leaves the object it was pointed at afterwards alone.
//
// This is the case that pins the design of the member-access arm rather than
// its existence. Resolving the property from inside the update callback -- the
// obvious shape, that being where the write is performed -- would follow the
// reassigned handle, put 8'hA5 on `other` and leave the original object at the
// 8'h11 the blocking assignment gave it. Each object is read back through a
// handle that still designates it, `keep` for the original and `other` for the
// second, so the pair of expectations tells those two outcomes apart instead of
// reporting one number that either could produce. The two starting values 8'h11
// and 8'h22 differ for the same reason: equal ones would leave each read unable
// to say which object it found.
TEST(NonblockingAssignSim, ClassHandleInTheTargetIsResolvedAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  logic [7:0] f;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  C other;\n"
      "  C keep;\n"
      "  logic [7:0] r;\n"
      "  logic [7:0] seen;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    other = new;\n"
      "    keep = h;\n"
      "    h.f = 8'h11;\n"
      "    other.f = 8'h22;\n"
      "    h.f <= 8'hA5;\n"
      "    h = other;\n"
      "    #1 r = keep.f;\n"
      "    seen = other.f;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r", 0xA5u}, {"seen", 0x22u}});
}

}  // namespace
