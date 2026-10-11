#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequenceEventSim, ProcessBlocksUntilSequenceEndpoint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  logic [7:0] result;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; result = 0;\n"
      "    #1 a = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 c = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    @(abc) result = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SequenceEventSim, MultipleWaitersOnSequenceEndpoint) {
  SimFixture f;
  auto* v1 = RunAndFindVar(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] r1, r2;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; r1 = 0; r2 = 0;\n"
      "    #1 a = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    @(ab) r1 = 8'd10;\n"
      "  end\n"
      "  initial begin\n"
      "    @(ab) r2 = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "r1");
  ASSERT_NE(v1, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);

  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
}

TEST(SequenceEventSim, ProcessStaysBlockedWhenSequenceNeverMatches) {
  // §9.4.2.4: the process executing the event control shall block until the
  // sequence reaches its end point. This is the blocking half of the rule:
  // the sequence `a ##1 b ##1 c` never completes because c is held low, so
  // the endpoint never fires and the waiting process never runs its action.
  // result must keep its initial value.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  logic [7:0] result;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; result = 0;\n"
      "    #1 a = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; #1 clk = 1; #1 clk = 0;\n"
      "    #1 clk = 1; #1 clk = 0;\n"  // c stays 0 -> no full match
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    @(abc) result = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.1 with §9.4.2.4: a sequence instance or-ed with another event is one
// operand among the others, so the edge wakes the process though the sequence
// never matches.
TEST(SequenceEventSim, AnOrListWakesOnItsOtherOperands) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic clk = 0, a = 0;\n"
                       "  sequence s1; @(posedge clk) a; endsequence\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin\n"
                       "    @(s1 or posedge clk);\n"
                       "    $display(\"woke %0t\", $time);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "woke 5\n");
}

// §9.4.2.3: an iff qualifier on a sequence instance lets a match wake the
// process only where its condition holds, so the match at 5 passes it by.
TEST(SequenceEventSim, AnIffQualifierGatesTheSequence) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic clk = 0, a = 1; bit en = 0;\n"
                       "  sequence s1; @(posedge clk) a; endsequence\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial #12 en = 1;\n"
                       "  initial begin\n"
                       "    @(s1 iff en);\n"
                       "    $display(\"woke %0t\", $time);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "woke 15\n");
}

// §9.4.2.1: an or-ed event control resumes its process once, on the first
// operand to occur, so s2's later match leaves the process in its delay.
TEST(SequenceEventSim, TwoSequencesResumeTheProcessOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; logic clk = 0, a = 1, b = 0;\n"
                       "  sequence s1; @(posedge clk) a; endsequence\n"
                       "  sequence s2; @(posedge clk) b; endsequence\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial #12 b = 1;\n"
                       "  initial begin\n"
                       "    @(s1 or s2);\n"
                       "    #100 $display(\"done %0t\", $time);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "done 105\n");
}

}  // namespace
