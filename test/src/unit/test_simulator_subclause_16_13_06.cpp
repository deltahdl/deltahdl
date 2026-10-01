#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/sequence_methods.sv around one destination
// sequence: the clause's e1 on sysclk, rising at 8, 24, 40, ..., ends at
// 56, and a destination sequence on the clock its body names; the process
// counts the end points the destination reaches and keeps the time of the
// last. clk rises at 5, 15, ..., never together with sysclk.
std::string SequenceMethodSource(const std::string& destination) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic sysclk = 0;\n"
         "  logic a = 0, b = 0, c = 0;\n"
         "  logic reset = 0, inst = 0, branch_back = 0;\n"
         "  logic reset1 = 0, branch_back1 = 0;\n"
         "  int ends = 0;\n"
         "  int last_end = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1;\n"
         "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e2_with_arg(sequence subseq);\n"
         "    @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 "
         "branch_back;\n"
         "  endsequence\n"
         "  sequence dest;\n" +
         destination +
         "  endsequence\n"
         "  initial forever begin\n"
         "    wait (dest.triggered);\n"
         "    ends++;\n"
         "    last_end = $time;\n"
         "    #1;\n"
         "  end\n"
         "  initial begin\n"
         "    #10 a = 1;\n"
         "    #10 reset = 1;\n"
         "    #10 reset = 0; b = 1;\n"
         "    #5 inst = 1;\n"
         "    #10 inst = 0;\n"
         "    #5 b = 0; c = 1; reset1 = 1;\n"
         "    #10 reset1 = 0;\n"
         "    #5 c = 0; branch_back = 1;\n"
         "    #5 branch_back1 = 1;\n"
         "    #5 branch_back = 0;\n"
         "    #5 branch_back1 = 0;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// The end points the destination sequence reached, and the time of the
// last.
struct EndPoints {
  uint64_t ends;
  uint64_t last_end;
};

EndPoints EndPointsOf(const std::string& destination) {
  SimFixture f;
  auto* ends = RunAndFindVar(SequenceMethodSource(destination), f, "ends");
  if (ends == nullptr) return {~0ull, ~0ull};
  Variable* last_end = f.ctx.FindVariable("last_end");
  return {ends->value.ToUint64(), last_end->value.ToUint64()};
}

// §16.13.6: triggered on a named sequence is true at the time step its end
// point is reached, 56 for e1, so the clause's e2, on e1's clock, reads it
// there and ends at branch_back, 72.
TEST(SequenceMethods, TriggeredOnANamedSequenceReadsItsEndPoint) {
  EndPoints e2 = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 "
      "branch_back;\n");
  EXPECT_EQ(e2.ends, 1u);
  EXPECT_EQ(e2.last_end, 72u);
}

// §16.13.6: matched on a named sequence stores its end point until the
// first tick of the reading clock after it, 65 on clk for e1's 56, so the
// clause's e3 reads it there and ends at branch_back1, 75.
TEST(SequenceMethods, MatchedOnANamedSequenceStoresItsEndPointForAnotherClock) {
  EndPoints e3 = EndPointsOf(
      "    @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;\n");
  EXPECT_EQ(e3.ends, 1u);
  EXPECT_EQ(e3.last_end, 75u);
}

// §16.13.6: triggered on a formal of type sequence reads the end point of
// the actual, e1's body passed to e2_with_arg, so the clause's e4 ends
// where e2 does, 72.
TEST(SequenceMethods, TriggeredOnASequenceFormalReadsTheActualsEndPoint) {
  EndPoints e4 =
      EndPointsOf("    e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 1u);
  EXPECT_EQ(e4.last_end, 72u);
}

// §16.13.6: the formal's triggered is the actual's end point and not the
// instance's own progress: an actual that never ends, $rose(reset1) at 56
// followed by b at 72 where b is low, leaves it false and the instance
// never ends.
TEST(SequenceMethods, AnActualThatNeverMatchesLeavesTheFormalsTriggeredFalse) {
  EndPoints e4 = EndPointsOf(
      "    e2_with_arg(@(posedge sysclk) $rose(reset1) ##1 b ##1 c);\n");
  EXPECT_EQ(e4.ends, 0u);
}

// §16.13.6 with §23.9: a sequence declared in an instantiated module has an
// end point of its own in each instance, which `triggered` waited on in the
// instance sees: each of u and w counts the ends of a ##1 a at 15 and 25 of
// its own a, u's high from 2 to 32 and w's never. The instance's sequence had
// no monitor, and its end point was never reached.
TEST(SequenceMethods, TriggeredInAnInstanceReadsItsOwnEndPoint) {
  SimFixture f;
  auto* u_hits = RunAndFindVar(
      "module child(input logic a, input logic clk);\n"
      "  int hits = 0;\n"
      "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
      "  initial forever begin\n"
      "    wait (s.triggered);\n"
      "    hits = hits + 1;\n"
      "    @(posedge clk);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0, a = 0, never = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  child u(a, clk);\n"
      "  child w(never, clk);\n"
      "  initial begin #2 a = 1; #30 a = 0; #20 $finish; end\n"
      "endmodule\n",
      f, "u.hits");
  ASSERT_NE(u_hits, nullptr);
  EXPECT_EQ(u_hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("w.hits")->value.ToUint64(), 0u);
}

// §16.13.6 with §23.6: `triggered` read through a hierarchical name, u.s,
// reads the end point of the sequence s of the instance the name selects, a
// wait on it resuming there: u's s ends at 15 and 25, its v1 high from 2 to
// 22, and w's s, its v1 never high, ends nowhere, so the waits on u.s resume
// twice, the last at 25, and those on w.s never.
TEST(SequenceMethods, TriggeredThroughAHierarchicalNameReadsThatInstances) {
  SimFixture f;
  auto* u_hits = RunAndFindVar(
      "module m(input logic clk, input logic v1);\n"
      "  logic v2 = 1;\n"
      "  sequence s; @(posedge clk) v1 ##1 v2; endsequence\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0, a = 0, never = 0;\n"
      "  int u_hits = 0, w_hits = 0, last = 0;\n"
      "  m u(clk, a);\n"
      "  m w(clk, never);\n"
      "  initial forever begin\n"
      "    wait (u.s.triggered);\n"
      "    u_hits++;\n"
      "    last = $time;\n"
      "    #1;\n"
      "  end\n"
      "  initial forever begin\n"
      "    wait (w.s.triggered);\n"
      "    w_hits++;\n"
      "    #1;\n"
      "  end\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #2 a = 1; #20 a = 0; #30 $finish; end\n"
      "endmodule\n",
      f, "u_hits");
  ASSERT_NE(u_hits, nullptr);
  EXPECT_EQ(u_hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
  EXPECT_EQ(f.ctx.FindVariable("w_hits")->value.ToUint64(), 0u);
}

// §16.13.6: the triggered status of a sequence is set in the Observed region
// of the time step its end point is reached at and persists to the end of the
// time step: s ends at 15 and 25, so a process waking at those posedges reads
// `s.triggered` in the Active region, before the status is set, and counts
// none, while a wait on it resumes after the Observed region and counts both.
TEST(SequenceMethods, TriggeredIsSetInTheObservedRegion) {
  SimFixture f;
  auto* active_hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, v1 = 0, v2 = 1;\n"
      "  int active_hits = 0, waited_hits = 0;\n"
      "  sequence s; @(posedge clk) v1 ##1 v2; endsequence\n"
      "  always @(posedge clk) if (s.triggered) active_hits++;\n"
      "  initial forever begin\n"
      "    wait (s.triggered);\n"
      "    waited_hits++;\n"
      "    @(posedge clk);\n"
      "  end\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #2 v1 = 1; #20 v1 = 0; #30 $finish; end\n"
      "endmodule\n",
      f, "active_hits");
  ASSERT_NE(active_hits, nullptr);
  EXPECT_EQ(active_hits->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("waited_hits")->value.ToUint64(), 2u);
}

}  // namespace
