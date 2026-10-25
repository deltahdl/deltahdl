#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_sequence_ticks.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.10: a new copy of each local variable is created at the beginning of
// each attempt and the initialization assignments are performed in the
// order the locals are declared, one's expression reading a local declared
// before it as assigned. `int v = te1, w = v + 1` gives w 2 at an attempt
// beginning where te1 is high, so with te1 and te2 at tick 3 `te2 ##1 (w ==
// 2)` ends at 4, the tick at 35; with te1 low at 3, w is 1 and it does not.
TEST(SequenceLocals, InitializationAssignmentsRunInDeclarationOrder) {
  const std::string kLocals = "    int v = te1, w = v + 1;\n";
  SimFixture f;
  auto* set = RunAndFindVar(
      SequenceTickSource("te2 ##1 (w == 2)", DriveTicks({{3}, {3}, {}, {}, {}}),
                         "", kLocals),
      f, "hits");
  ASSERT_NE(set, nullptr);
  EXPECT_EQ(set->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* clear = RunAndFindVar(
      SequenceTickSource("te2 ##1 (w == 2)", DriveTicks({{}, {3}, {}, {}, {}}),
                         "", kLocals),
      g, "hits");
  ASSERT_NE(clear, nullptr);
  EXPECT_EQ(clear->value.ToUint64(), 0u);
}

// Expects the sequence `body`, declaring `locals` and its module the items
// `prelude`, to end once, at 4, the tick at 35, with te2 high at 3 alone.
void ExpectOneEndAtFour(const std::string& body, const std::string& locals,
                        const std::string& prelude = "") {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource(body, DriveTicks({{}, {3}, {}, {}, {}}),
                                       prelude, locals),
                    f, "hits");
  ASSERT_NE(hits, nullptr) << body;
  EXPECT_EQ(hits->value.ToUint64(), 1u) << body;
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u) << body;
}

// Expects the sequence `te2 ##1 last_operand`, declaring `locals` and its
// module the items `prelude`, to end once, at 4, the tick at 35, with te2
// high at 3 alone.
void ExpectOneEndAfterTe2(const std::string& last_operand,
                          const std::string& locals,
                          const std::string& prelude = "") {
  ExpectOneEndAtFour("te2 ##1 " + last_operand, locals, prelude);
}

// §16.10 with §7.4.1: a sequence's local declared of a packed type, `logic
// [3:0] x = 29`, holds the four bits 13 of its initialization, so with te2
// at 3 `te2 ##1 (x == 13)` ends at 4, the tick at 35; a 32-bit x would hold
// 29 and a 1-bit x 1 (#5745).
TEST(SequenceLocals, APackedLocalHoldsItsDeclaredWidth) {
  ExpectOneEndAfterTe2("(x == 13)", "    logic [3:0] x = 29;\n");
}

// §16.10 with §6.11 and §11.8.1: a sequence's int local is signed, so -1 is
// below 0 where an operand reads it, and where a later local's
// initialization does (#5770).
TEST(SequenceLocals, AnIntLocalReadsAsSigned) {
  ExpectOneEndAfterTe2("(x < 0)", "    int x = -1;\n");
  ExpectOneEndAfterTe2("y", "    int x = -1;\n    bit y = x < 0;\n");
}

// §16.10 with §6.11: a sequence's local takes the signedness its signing
// keyword writes: `logic signed [3:0]` holding -1 is below 0, and `int
// unsigned` holding -1 above it (#5768).
TEST(SequenceLocals, ALocalTakesTheSignednessItsKeywordWrites) {
  ExpectOneEndAfterTe2("(x < 0)", "    logic signed [3:0] x = -1;\n");
  ExpectOneEndAfterTe2("(x > 0)", "    int unsigned x = -1;\n");
}

// The types the cases of a local declared with a type name use (§6.18).
constexpr char kNibbleTypes[] =
    "  typedef logic [3:0] nib_t;\n"
    "  typedef logic signed [3:0] snib_t;\n"
    "  typedef bit [3:0] bnib_t;\n";

// §16.10 with §6.18: a sequence's local declared with a type name is of the
// type the name stands for: nib_t is four 4-state unsigned bits, keeping 13
// of 29 and x of 'x, bnib_t four 2-state ones, keeping 0 of 'x (#7624),
// snib_t four signed ones, below 0 at -1, and `nib_t [1:0]` two nib_t, eight
// bits keeping 255 of 9'h1FF (#5767). §16.10 bars reading a local never
// assigned, so each is given a value.
TEST(SequenceLocals, ALocalOfATypeNameIsTheTypeTheNameStandsFor) {
  ExpectOneEndAfterTe2("(x == 13)", "    nib_t x = 29;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("$isunknown(x)", "    nib_t x = 'x;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x == 0)", "    bnib_t x = 'x;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x < 0)", "    snib_t x = -1;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x == 255)", "    nib_t [1:0] x = 9'h1FF;\n",
                       kNibbleTypes);
}

// §16.10 with A.10 footnote 51: a match item may assign a select of a
// sequence's local, writing those bits and keeping the rest. From v 8'h1F,
// `v[1] = 0` leaves 8'h1D, `v[7:6] = 2'b11` 8'hDF, `v[3:0] += 3` 8'h12, its
// four bits wrapping where the whole local would reach 8'h22, `v[7:4]++`
// 8'h2F where `v++` gives 8'h20, and `--v[4]` 8'h0F where `--v` gives 8'h1E.
// Each, attached to te2 at 3, ends `##1 (v == want)` at 4; a target read as
// a bare name alone left the group unparsed and the sequence ending nowhere
// (#8091).
TEST(SequenceLocals, AMatchItemAssignsASelectOfTheLocal) {
  struct Case {
    const char* item;
    const char* want;
  };
  const Case kCases[] = {{"v[1] = 0", "8'h1D"},
                         {"v[7:6] = 2'b11", "8'hDF"},
                         {"v[3:0] += 3", "8'h12"},
                         {"v[7:4]++", "8'h2F"},
                         {"--v[4]", "8'h0F"}};
  for (const Case& c : kCases) {
    ExpectOneEndAtFour(
        std::string("(te2, ") + c.item + ") ##1 (v == " + c.want + ")",
        "    logic [7:0] v = 8'h1F;\n");
  }
}

// §16.10 with A.10 footnote 51: the select a match item assigns reaches the
// local it names through an instance, as the whole local is reached: sub's own
// w, renamed for the instance, and the local v passed to sub's formal lv.
// `w[1] = 0` and `lv[1] = 0` each take 8'h1F to 8'h1D, so with te2 at 3 both
// sequences end at 4 (#8091).
TEST(SequenceLocals, AMatchItemAssignsASelectOfALocalReachedThroughAnInstance) {
  ExpectOneEndAtFour("sub", "",
                     "  sequence sub; logic [7:0] w = 8'h1F;\n"
                     "    (te2, w[1] = 0) ##1 (w == 8'h1D);\n"
                     "  endsequence\n");
  ExpectOneEndAtFour("sub(v) ##1 (v == 8'h1D)", "    logic [7:0] v = 8'h1F;\n",
                     "  sequence sub(lv); (te2, lv[1] = 0); endsequence\n");
}

// The structure the cases of a local of a packed structure type use (§7.2).
constexpr char kPairType[] =
    "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n";

// §16.10 with §7.2: a sequence's local of a packed structure type reads and
// writes its members by name. p, a pair_t holding 8'h3C, has p.hi 3 and p.lo
// 12, read by an operand and by a later local's initialization; `p.lo = 5`
// leaves it 8'h35, and `p.hi += 1` 8'h4C (#8094, #8091).
TEST(SequenceLocals, AStructureLocalReadsAndWritesItsMembers) {
  const std::string kLocal = "    pair_t p = 8'h3C;\n";
  ExpectOneEndAfterTe2("(p.hi == 3 && p.lo == 12)", kLocal, kPairType);
  ExpectOneEndAfterTe2("(h == 3)", kLocal + "    logic [3:0] h = p.hi;\n",
                       kPairType);
  ExpectOneEndAtFour("(te2, p.lo = 5) ##1 (p == 8'h35)", kLocal, kPairType);
  ExpectOneEndAtFour("(te2, p.hi += 1) ##1 (p == 8'h4C)", kLocal, kPairType);
}

// §16.10 with §7.4.1: a select of a sequence's local resolves against the
// dimensions it was declared with. `logic [8:1] v` holding 1 has v[1] 1 and
// v[2] 0, where [7:0] reads them the other way round, read by an operand and
// by a later local's initialization, and `v[1] = 0` clears the bit holding
// the 1. Holding 8'hA5, `nib_t [1:0] x` has x[1] the nibble 4'hA and x[0]
// 4'h5, and `logic [1:0][3:0] y` y[1] 4'hA and y[0][0] 1, where one bit
// apiece would read 0 and 1 (#8095).
TEST(SequenceLocals, ASelectOfALocalResolvesAgainstItsDeclaredDimensions) {
  const std::string kVector = "    logic [8:1] v = 1;\n";
  ExpectOneEndAfterTe2("(v[1] == 1 && v[2] == 0)", kVector);
  ExpectOneEndAfterTe2("b", kVector + "    bit b = v[1];\n");
  ExpectOneEndAtFour("(te2, v[1] = 0) ##1 (v == 0)", kVector);
  ExpectOneEndAfterTe2("(x[1] == 4'hA && x[0] == 4'h5)",
                       "    nib_t [1:0] x = 8'hA5;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(y[1] == 4'hA && y[0][0] == 1)",
                       "    logic [1:0][3:0] y = 8'hA5;\n");
}

// §16.10 makes a local's initialization an assignment to it, and §6.11.2 has
// an assignment to a 2-state variable turn the x and z bits of a 4-state value
// to 0: a `bit [3:0]` local initialized with 'x and an `int` one with 'z each
// hold 0, where one keeping the unknown bits would leave `x == 0` unknown and
// the sequence unmatched (#7624).
TEST(SequenceLocals, ATwoStateLocalDropsTheUnknownBitsOfItsInitialization) {
  ExpectOneEndAfterTe2("(x == 0)", "    bit [3:0] x = 'x;\n");
  ExpectOneEndAfterTe2("(x == 0)", "    int x = 'z;\n");
}

// §16.10 with §6.11: a sequence's time local is 64 bits, unsigned and
// four-state: -1 is all 64 bits set, above any 32-bit value, and the local
// keeps the x of 'x (#5769). §16.10 bars reading a local never assigned, so
// it is given one.
TEST(SequenceLocals, ATimeLocalIsSixtyFourUnsignedFourStateBits) {
  ExpectOneEndAfterTe2("(t > 64'hFFFF_FFFF)", "    time t = -1;\n");
  ExpectOneEndAfterTe2("$isunknown(t)", "    time t = 'x;\n");
}

// §16.10: the match items attached to a subsequence are performed at the end
// of each nonempty match of it, in the order written, so `(te2[->1], x = 1,
// y = x + 1)` leaves y 2; te1 at 1 and te2 at 3 end `te1 ##1 (te2[->1], x =
// 1, y = x + 1) ##1 (y == 2)` at 4, the tick at 35.
TEST(SequenceLocals, MatchItemsRunInOrderAtTheSubsequenceEnd) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1 ##1 (te2[->1], x = 1, y = x + 1) ##1 (y == 2)",
                         DriveTicks({{1}, {3}, {}, {}, {}}), "",
                         "    int x, y;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

// §16.10: match items attached to the operand of a repetition accumulate
// over its iterations. `(te1[->1], x += 2)[*3]` with te1 at 2, 4 and 6
// leaves x 6, so `##1 (x == 6)` ends at 7, the tick at 65.
TEST(SequenceLocals, AssignmentsOnARepeatedOperandAccumulate) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("(te1[->1], x += 2)[*3] ##1 (x == 6)",
                                       DriveTicks({{2, 4, 6}, {}, {}, {}, {}}),
                                       "", "    int x = 0;\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 65u);
}

// §16.10: the clause's count_a_cycles over te1, `($rose(te1), x = 1) ##1
// (te1, x++)[*0:$] ##1 !te1 && (x <= 3)`, counts the ticks te1 stays high
// from its rise: high at 3 to 5 it ends at 6, the tick at 55, with x 3; high
// at 3 to 7 x reaches 5 and it does not end.
TEST(SequenceLocals, IncrementCountsTheRepeatedCondition) {
  const std::string kBody =
      "($rose(te1), x = 1) ##1 (te1, x++)[*0:$] ##1 !te1 && (x <= 3)";
  SimFixture f;
  auto* three = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5}, {}, {}, {}, {}}), "",
                         "    int x;\n"),
      f, "hits");
  ASSERT_NE(three, nullptr);
  EXPECT_EQ(three->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* five = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5, 6, 7}, {}, {}, {}, {}}),
                         "", "    int x;\n"),
      g, "hits");
  ASSERT_NE(five, nullptr);
  EXPECT_EQ(five->value.ToUint64(), 0u);
}

// §16.10: a local variable passed as an entire actual argument to an untyped
// formal of a named sequence is bound to the formal, and an assignment to the
// formal in the instance is an assignment to the local, read in the
// instantiating context after the instance matches. sub(lv) assigns lv 1
// where te2 holds, so `te1 ##1 sub(v) ##1 (v == 1)` with te1 at 1 and te2
// at 2 ends at 3, the tick at 25.
TEST(SequenceLocals, LocalPassedAsActualIsBoundToTheFormal) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("te1 ##1 sub(v) ##1 (v == 1)",
                                       DriveTicks({{1}, {2}, {}, {}, {}}),
                                       "  sequence sub(lv);\n"
                                       "    (te2, lv = 1);\n"
                                       "  endsequence\n",
                                       "    int v;\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// A design whose property `pr` declares the local `decl`, `int x` unless
// given, after the module items `items`, and is `@(posedge clk) body`,
// asserted with a pass and a fail count:
// clk rises at 5, 15 and so on to 95 and v counts its rising edges, so v
// reads k at the k-th of them from 0, and the run ends at 100, between two
// rising edges.
std::string PropertyLocalSource(const std::string& body,
                                const std::string& decl,
                                const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int v = 0, p = 0, f = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) v <= v + 1;\n" +
         items +
         "  property pr;\n"
         "    " +
         decl +
         ";\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endproperty\n"
         "  assert property (pr) p++; else f++;\n"
         "  initial #100 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts a run of PropertyLocalSource(body, decl, items)
// leaves.
void ExpectPropertyCounts(const std::string& body, uint64_t passes,
                          uint64_t fails, const std::string& decl = "int x",
                          const std::string& items = "") {
  SimFixture f;
  auto* p = RunAndFindVar(PropertyLocalSource(body, decl, items), f, "p");
  ASSERT_NE(p, nullptr) << body;
  EXPECT_EQ(p->value.ToUint64(), passes) << body;
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), fails) << body;
}

// §16.10: a local declared in a property is assigned by a match item and
// read later in the same attempt, as the clause's pipeline property `e`
// assigns x in the antecedent of `|->` and reads it in the consequent. The
// attempt at the k-th edge assigns x = k and one edge later finds v == k +
// 1, so the nine attempts that complete by the end, from the edges 0 to 8,
// all pass, through `|-> ##1` as through `|=>`; comparing against k + 2
// instead fails all nine, so the local is read and not ignored.
TEST(PropertyLocals, AntecedentAssignmentReachesTheConsequent) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 (v == x + 1)", 9, 0);
  ExpectPropertyCounts("(1, x = v) |=> (v == x + 1)", 9, 0);
  ExpectPropertyCounts("(1, x = v) |-> ##1 (v == x + 2)", 0, 9);
}

// §16.10: within a property whose body is a sequence, a later operand reads
// what an earlier operand's match item assigned the property's local.
TEST(PropertyLocals, SequenceBodyReadsItsEarlierAssignment) {
  ExpectPropertyCounts("(1, x = v) ##1 (v == x + 1)", 9, 0);
}

// §16.10: a local may be reassigned later in the property, a compound
// assignment reading the value it holds: x = k at the attempt's edge, x += 1
// one edge later, and at the edge after that v == k + 2 == x + 1, so the
// eight attempts from the edges 0 to 7 pass.
TEST(PropertyLocals, ConsequentReassignsTheLocal) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 (1, x += 1) ##1 (v == x + 1)", 8, 0);
}

// §16.10: each evaluation attempt creates its own copy of the property's
// locals. With `##2` the attempt from edge k is still waiting when the
// attempts from k + 1 and k + 2 assign their x, so a copy shared between
// attempts would hold k + 2 at its check; with a copy each, the eight
// attempts from the edges 0 to 7 all find v == x + 2.
TEST(PropertyLocals, EachAttemptHoldsItsOwnCopy) {
  ExpectPropertyCounts("(1, x = v) |-> ##2 (v == x + 2)", 8, 0);
}

// §16.10 with §7.4.1: a property's local declared of a packed type, `logic
// [3:0] x`, holds four unsigned bits. x = k + 12 wraps below 12 for the
// attempts from the edges 4 to 8, which pass, and stays at 12 or above for
// those from 0 to 3, which fail; a 32-bit x would fail all nine, and a 1-bit
// x, or one read as signed as the int it is assigned from, pass all nine
// (#5745).
TEST(PropertyLocals, APackedLocalHoldsItsDeclaredWidth) {
  ExpectPropertyCounts("(1, x = v + 12) |-> ##1 (x < 12)", 5, 4,
                       "logic [3:0] x");
}

// §16.10 with §6.11: a property's local holds the signedness of its type,
// whatever the expression assigned to it: an int assigned the unsigned
// 32'hFFFF_FFFF is -1, below 0 at all nine attempts, where a copy taking the
// assigned value's signedness would be 4294967295 and fail them all.
TEST(PropertyLocals, AnIntLocalIsSignedWhateverItIsAssigned) {
  ExpectPropertyCounts("(1, x = 32'hFFFF_FFFF) |-> ##1 (x < 0)", 9, 0);
}

// §16.10 with §6.11: a property's local declared `logic signed [3:0]` is
// signed, so -1 assigned to it is below 0 at all nine attempts (#5768).
TEST(PropertyLocals, ASignedPackedLocalIsSigned) {
  ExpectPropertyCounts("(1, x = -1) |-> ##1 (x < 0)", 9, 0,
                       "logic signed [3:0] x");
}

// §16.10 with §6.18: a property's local declared with a type name standing
// for four unsigned bits wraps as `logic [3:0]` does, x = k + 12 falling
// below 12 for the attempts from the edges 4 to 8 alone (#5767).
TEST(PropertyLocals, ALocalOfATypeNameIsTheTypeTheNameStandsFor) {
  ExpectPropertyCounts("(1, x = v + 12) |-> ##1 (x < 12)", 5, 4, "nib_t x",
                       "  typedef logic [3:0] nib_t;\n");
}

// §16.10 with §6.11: a property's time local is 64 bits and unsigned, so -1
// is above any 32-bit value at all nine attempts (#5769).
TEST(PropertyLocals, ATimeLocalIsSixtyFourUnsignedBits) {
  ExpectPropertyCounts("(1, x = -1) |-> ##1 (x > 64'hFFFF_FFFF)", 9, 0,
                       "time x");
}

// §16.10 with A.10 footnote 51: a match item may assign a select of a
// property's local, writing those bits of the attempt's copy and keeping the
// rest: from 8'hF0, `x[0] = 1` leaves 8'hF1 where `x = 1` gives 1, and from
// 8'hFF, `x[3:0] += 2` leaves 8'hF1, its four bits wrapping, where `x += 2`
// gives 8'h01, and `x[7:4]++` 8'h0F where `x++` gives 0. All nine attempts
// pass each; a target read as a bare name alone left the body unevaluated
// (#8091).
TEST(PropertyLocals, AMatchItemAssignsASelectOfTheLocal) {
  ExpectPropertyCounts("(1, x[0] = 1) |-> ##1 (x == 8'hF1)", 9, 0,
                       "logic [7:0] x = 8'hF0");
  ExpectPropertyCounts("(1, x[3:0] += 2) |-> ##1 (x == 8'hF1)", 9, 0,
                       "logic [7:0] x = 8'hFF");
  ExpectPropertyCounts("(1, x[7:4]++) |-> ##1 (x == 8'h0F)", 9, 0,
                       "logic [7:0] x = 8'hFF");
}

// §16.10 with §7.4.1: the copy of a property's packed local an attempt reads
// is four bits wide, as $bits finds it (#5745).
TEST(PropertyLocals, APackedLocalsCopyIsItsDeclaredWidth) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 ($bits(x) == 4)", 9, 0,
                       "logic [3:0] x");
}

// The source the cases of a local flowing out of `triggered` share: clk rises
// at 5, 15, ..., 95, and cnt counts its falls, so at the rise of 15 + 10k it is
// k + 1. `decls` declares the sequences, and c1 and c2 count the attempts of
// seq_a and seq_b, printed at 97.
std::string RunTriggeredFlowCase(const std::string& decls) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  int cnt = 0;\n"
      "  always @(negedge clk) cnt <= cnt + 1;\n"
      "  int c1 = 0, c2 = 0;\n" +
          decls +
          "  cover property (@(posedge clk) seq_a) c1++;\n"
          "  cover property (@(posedge clk) seq_b) c2++;\n"
          "  initial #97 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "endmodule\n",
      f);
}

// §16.10: a local passed as an entire actual to an instance to which
// `triggered` is applied, the whole Boolean, flows out of it with the value
// the instance's match assigned, as it does from the plain instance: v1 holds
// the cnt of the tick before, which cnt exceeds by two a tick later, at each
// attempt from 15 to 85. A match item of the operand reads the value, and v2,
// passed to nothing, is the reading sequence's alone.
TEST(SequenceLocals, ALocalFlowsOutOfTriggered) {
  std::string out = RunTriggeredFlowCase(
      "  sequence sub(lv, src); @(posedge clk) (1, lv = src) ##1 1;\n"
      "  endsequence\n"
      "  sequence seq_a; int v1, v2;\n"
      "    (sub(v1, cnt).triggered, v2 = v1) ##1 (cnt == v2 + 2);\n"
      "  endsequence\n"
      "  sequence seq_b; int v1;\n"
      "    sub(v1, cnt) ##1 (cnt == v1 + 2);\n"
      "  endsequence\n");
  EXPECT_NE(out.find("c1=8 c2=8\n"), std::string::npos);
}

// §16.10: where two matches of the instance end at the tick `triggered` is
// read at, each flows its own value, the one begun a tick before and the one
// begun two before, so a read wanting either finds it: cnt two past v1 from
// the attempt of 15, and three past from the attempt of 25, the first with
// two matches ending at it. The instance's own local w, passed to nothing,
// stays in it.
TEST(SequenceLocals, EachMatchEndingAtTheTickFlowsItsOwnValue) {
  std::string out = RunTriggeredFlowCase(
      "  sequence sub(lv, src); bit w;\n"
      "    @(posedge clk) (1, lv = src, w = 1) ##[1:2] w;\n"
      "  endsequence\n"
      "  sequence seq_a; int v1;\n"
      "    sub(v1, cnt + 0).triggered ##1 (cnt == v1 + 2);\n"
      "  endsequence\n"
      "  sequence seq_b; int v1;\n"
      "    sub(v1, cnt + 0).triggered ##1 (cnt == v1 + 3);\n"
      "  endsequence\n");
  EXPECT_NE(out.find("c1=8 c2=7\n"), std::string::npos);
}

// §16.10: a group's match items are performed once, at the end of each match
// of its sequence_expr, though the operand ending it repeats. After `(te1, x
// = 0)` at tick 1, `(te2[*2], x += 1)` with te2 at 2 and 3 adds 1 once, at
// 3, so `##1 (x == 1)` ends at 4, the tick at 35; `(te2[->2], x += 1)` with
// te2 at 2 and 4 adds it once, at 4, ending the sequence at 5, the tick at
// 45.
TEST(SequenceLocals, AGroupsItemsAfterARepeatedOperandRunOnce) {
  struct Case {
    const char* group;
    std::vector<int> te2;
    uint64_t last;
  };
  const Case kCases[] = {
      {"(te2[*2], x += 1)", {2, 3}, 35},
      {"(te2[->2], x += 1)", {2, 4}, 45},
  };
  for (const Case& c : kCases) {
    SCOPED_TRACE(c.group);
    SimFixture f;
    auto* hits = RunAndFindVar(
        SequenceTickSource(
            std::string("(te1, x = 0) ##1 ") + c.group + " ##1 (x == 1)",
            DriveTicks({{1}, c.te2, {}, {}, {}}), "", "    int x;\n"),
        f, "hits");
    ASSERT_NE(hits, nullptr);
    EXPECT_EQ(hits->value.ToUint64(), 1u);
    EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), c.last);
  }
}

}  // namespace
