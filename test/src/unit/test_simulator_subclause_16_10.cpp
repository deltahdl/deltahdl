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

// A design whose property `pr` declares `int x` and is `@(posedge clk)
// body`, asserted with a pass and a fail count: clk rises at 5, 15 and so on
// to 95 and v counts its rising edges, so v reads k at the k-th of them from
// 0, and the run ends at 100, between two rising edges.
std::string PropertyLocalSource(const std::string& body) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int v = 0, p = 0, f = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) v <= v + 1;\n"
         "  property pr;\n"
         "    int x;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endproperty\n"
         "  assert property (pr) p++; else f++;\n"
         "  initial #100 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts a run of PropertyLocalSource(body) leaves.
void ExpectPropertyCounts(const std::string& body, uint64_t passes,
                          uint64_t fails) {
  SimFixture f;
  auto* p = RunAndFindVar(PropertyLocalSource(body), f, "p");
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

}  // namespace
