#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TimingControlSimulation, DelayControlSuspendsExecution) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #10 x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(TimingControlSimulation, DelayControlZeroAdvances) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #0 x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 2u);
}

TEST(TimingControlSimulation, DelayControlNullStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    #1 ;\n"
      "    x = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 10u);
}

TEST(TimingControlSimulation, DelayControlSequentialDelays) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 x = x + 8'd1;\n"
      "    #5 x = x + 8'd1;\n"
      "    #5 x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

TEST(TimingControlSimulation, EventControlStarWaitsAnyChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, y;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    y = 0;\n"
      "    #5 a = 8'd7;\n"
      "  end\n"
      "  always @(*) y = a;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 7u}});
}

TEST(TimingControlSimulation, BreakExitsLoop) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    for (int i = 0; i < 10; i++) begin\n"
      "      if (i == 3) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

TEST(TimingControlSimulation, ContinueSkipsIteration) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    for (int i = 0; i < 5; i++) begin\n"
      "      if (i == 2) continue;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 4u);
}

TEST(TimingControlSimulation, ReturnExitsFunction) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val();\n"
      "    return 8'd123;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_val();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 123u);
}

TEST(TimingControlSimulation, ReturnVoidExitsFunction) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_val();\n"
      "    x = 8'd44;\n"
      "    return;\n"
      "    x = 8'd99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    set_val();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 44u);
}

TEST(TimingControlSimulation, TwoProcessesSynchronizeViaDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #10 x = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    #20 y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}, {"y", 2u}});
}

// event_control ::= clocking_event ; clocking_event ::= @ ( event_expression )
// with an edge_identifier. A process suspended on @(posedge clk) resumes only
// when the driven net (§A.8.3 expression over a real signal) rises, at which
// point it captures y.
TEST(TimingControlSimulation, EventControlPosedgeResumesProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    y = 8'd9;\n"
      "    x = 8'd0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = y;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 9u}, {"clk", 1u}, {"y", 9u}});
}

// wait_statement ::= wait ( expression ) statement_or_null
// A process blocks until the condition expression (built over a real variable)
// becomes true, then runs its body.
TEST(TimingControlSimulation, WaitConditionResumesProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic go;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    go = 1'b0;\n"
      "    x = 8'd0;\n"
      "    #5 go = 1'b1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (go) x = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"go", 1u}});
}

// event_trigger ::= -> hierarchical_event_identifier ... ; combined with
// event_control on a named event. Built from a real `event` declaration
// (§6.17): triggering -> e wakes the process waiting on @(e).
TEST(TimingControlSimulation, NamedEventTriggerResumesWaiter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 -> e;\n"
      "  end\n"
      "  initial begin\n"
      "    @(e) x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 3u}});
}

}  // namespace
