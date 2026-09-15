#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.9.11 describes composing a complex sequence from simpler subsequences.
// One of its two methods is to detect the end point of another sequence with
// the triggered method: "When method triggered is evaluated in an expression,
// it tests whether its operand sequence has reached its end point at that
// particular point in time. The result of triggered does not depend upon the
// starting point of the match of its operand sequence."
//
// The production path exercised here is the live sequence monitor
// (simulator/sequence_monitor.cpp), which fires a named sequence's end-point
// event when its clocked linear body matches, and the member-access evaluation
// in simulator/eval_expr.cpp that turns `seq.triggered` into the single-bit
// end-point status for the current time step. The named sequences are declared
// and matched using real §16.8/§16.7 syntax and driven through the full
// parse/elaborate/lower/run pipeline.

// Two sequences reach their end point at the same clock tick even though their
// matches BEGAN at different ticks: the three-cycle sequence starts matching
// two ticks before the one-cycle sequence. Because triggered reports only the
// end point at that instant and has no bearing on where the match started, the
// composing process observes both sequences as triggered simultaneously.
TEST(SequenceCompositionSim, TriggeredReflectsEndpointIndependentOfStartPoint) {
  uint64_t result = RunAndGet(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  logic [7:0] result;\n"
      "  sequence long_seq;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"  // match starts at the a tick
      "  endsequence\n"
      "  sequence short_seq;\n"
      "    @(posedge clk) c;\n"  // match starts at the c tick
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; result = 0;\n"
      "    #1 a = 1; clk = 1; #1 clk = 0;\n"
      "    #1 a = 0; b = 1; clk = 1; #1 clk = 0;\n"
      "    #1 b = 0; c = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(long_seq.triggered);\n"
      "    result = (long_seq.triggered && short_seq.triggered) ? 8'd42\n"
      "                                                         : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  // Both end points coincide despite different start points, so the composed
  // expression evaluates both operands as true.
  EXPECT_EQ(result, 42u);
}

// §16.9.11: triggered's result is true (1'b1) or false (1'b0) and tests whether
// the operand sequence has reached its end point AT THAT PARTICULAR POINT IN
// TIME. When the end point has not been reached, the composed expression sees
// the false result. Here the sequence's match is in progress (its leading
// Boolean is held true across ticks, so attempts advance past the start) but
// the trailing Boolean never becomes true, so no end point is reached and the
// production end-point event never fires: triggered evaluates to 1'b0.
TEST(SequenceCompositionSim, TriggeredIsFalseWhenEndpointNotReached) {
  uint64_t result = RunAndGet(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] result;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 1; b = 0; result = 8'hee;\n"
      "    #1 clk = 1; #1 clk = 0;\n"  // a seen: an attempt starts and advances
      "    #1 clk = 1; #1 clk = 0;\n"  // b never true: end point not reached
      "    result = ab.triggered ? 8'd1 : 8'd0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0u);
}

// --- The clause's examples over the tick-driven module ---

// The module the cases below share: sysclk rises at 5, 15, 25, ..., tick n at
// 10n - 5, the tick counter counting through; trans, start_trans, a, b, c and
// end_trans are high at ticks 1 to 6 in turn; reset, inst, proc1, proc2 and
// branch_back at 11 to 14 and again at 21, 22, 24, 25 and 26, ready from 11
// to 13 and from 23 to 25; and req at 31 and 32. `decls` declares the
// sequences and a process counts the ticks at which `watched` reaches its
// end point.
std::string CompositionSource(const std::string& decls,
                              const std::string& watched) {
  return "module t;\n"
         "  logic sysclk = 0;\n"
         "  int tick = 1;\n"
         "  logic trans, start_trans, a, b, c, end_trans;\n"
         "  logic reset, inst, ready, proc1, proc2, branch_back, req;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 sysclk = ~sysclk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign trans = tick inside {1};\n"
         "  assign start_trans = tick inside {2};\n"
         "  assign a = tick inside {3};\n"
         "  assign b = tick inside {4};\n"
         "  assign c = tick inside {5};\n"
         "  assign end_trans = tick inside {6};\n"
         "  assign reset = tick inside {11, 21};\n"
         "  assign inst = tick inside {12, 22};\n"
         "  assign ready = tick inside {11, 12, 13, 23, 24, 25};\n"
         "  assign proc1 = tick inside {12, 24};\n"
         "  assign proc2 = tick inside {13, 25};\n"
         "  assign branch_back = tick inside {14, 26};\n"
         "  assign req = tick inside {31, 32};\n" +
         decls +
         "  initial forever begin\n"
         "    wait (" +
         watched +
         ".triggered);\n"
         "    hits = hits + 1;\n"
         "    last = tick;\n"
         "    @(posedge sysclk);\n"
         "  end\n"
         "  initial #350 $finish;\n"
         "endmodule\n";
}

const char* const kE1 =
    "  sequence e1;\n"
    "    @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2;\n"
    "  endsequence\n";

// §16.9.11: a named sequence referenced by name must match from the tick the
// reference is reached at: s, `a ##1 b ##1 c`, matches from tick 3, the tick
// after start_trans, so rule ends at 6 with end_trans.
TEST(SequenceComposition, InstanceMatchesFromTheTickItIsReached) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CompositionSource("  sequence s;\n"
                        "    a ##1 b ##1 c;\n"
                        "  endsequence\n"
                        "  sequence rule;\n"
                        "    @(posedge sysclk) trans ##1 start_trans ##1 s ##1 "
                        "end_trans;\n"
                        "  endsequence\n",
                        "rule"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 6u);
}

// §16.9.11: e1.triggered as an operand is true at a tick e1 reaches its end
// point at, whatever the match's start, where an instance of e1 must match
// from that tick. e1 matches from 11 to 13, one tick after inst at 12, so
// `reset ##1 inst ##1 e1.triggered ##1 branch_back` ends at 14 and not at 26,
// where e1 has an end point at 25 only; `reset ##1 inst ##1 e1 ##1
// branch_back` needs e1 to match from 13 or 23, which it does from 23 alone,
// so it ends at 26 and not at 14.
TEST(SequenceComposition, TriggeredDetectsTheEndPointWhateverTheStart) {
  SimFixture f;
  auto* by_endpoint = RunAndFindVar(
      CompositionSource(std::string(kE1) +
                            "  sequence rule;\n"
                            "    @(posedge sysclk) reset ##1 inst ##1 "
                            "e1.triggered ##1 branch_back;\n"
                            "  endsequence\n",
                        "rule"),
      f, "hits");
  ASSERT_NE(by_endpoint, nullptr);
  EXPECT_EQ(by_endpoint->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 14u);
  SimFixture g;
  auto* by_instance = RunAndFindVar(
      CompositionSource(std::string(kE1) +
                            "  sequence rule;\n"
                            "    @(posedge sysclk) reset ##1 inst ##1 e1 ##1 "
                            "branch_back;\n"
                            "  endsequence\n",
                        "rule"),
      g, "hits");
  ASSERT_NE(by_instance, nullptr);
  EXPECT_EQ(by_instance->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 26u);
}

// §16.9.11: triggered applies to an instance with arguments, `e2(ready,
// proc1, proc2).triggered` being `e2_instantiated.triggered` for a sequence
// whose body is that instance; both end at 14.
TEST(SequenceComposition, TriggeredAppliesToAnInstanceWithArguments) {
  const std::string kE2 =
      "  sequence e2(a, b, c);\n"
      "    @(posedge sysclk) $rose(a) ##1 b ##1 c;\n"
      "  endsequence\n";
  SimFixture f;
  auto* direct = RunAndFindVar(
      CompositionSource(kE2 + "  sequence rule2;\n"
                              "    @(posedge sysclk) reset ##1 inst ##1 "
                              "e2(ready, proc1, proc2).triggered ##1 "
                              "branch_back;\n"
                              "  endsequence\n",
                        "rule2"),
      f, "hits");
  ASSERT_NE(direct, nullptr);
  EXPECT_EQ(direct->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 14u);
  SimFixture g;
  auto* named = RunAndFindVar(
      CompositionSource(kE2 + "  sequence e2_instantiated;\n"
                              "    e2(ready, proc1, proc2);\n"
                              "  endsequence\n"
                              "  sequence rule2a;\n"
                              "    @(posedge sysclk) reset ##1 inst ##1 "
                              "e2_instantiated.triggered ##1 branch_back;\n"
                              "  endsequence\n",
                        "rule2a"),
      g, "hits");
  ASSERT_NE(named, nullptr);
  EXPECT_EQ(named->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 14u);
}

// §16.9.11: a sequence's empty match does not activate triggered.
// zero_or_one_req, `(req==1'b1)[*0:1]`, admits the empty match at every
// tick, and reaches an end point that triggered reports at the two ticks
// req is high at alone.
TEST(SequenceComposition, EmptyMatchDoesNotActivateTriggeredLive) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      CompositionSource("  sequence zero_or_one_req;\n"
                        "    @(posedge sysclk) (req==1'b1)[*0:1];\n"
                        "  endsequence\n",
                        "zero_or_one_req"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 32u);
}

}  // namespace
