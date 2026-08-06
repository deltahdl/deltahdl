#include "helpers_scheduler.h"

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

}  // namespace
