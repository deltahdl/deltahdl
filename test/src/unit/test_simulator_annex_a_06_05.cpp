#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- delay_control simulation ---

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

// --- event_control simulation ---

TEST(TimingControlSimulation, EventControlPosedgeWaits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    x = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(TimingControlSimulation, EventControlNegedgeWaits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    x = 0;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
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

// --- wait_statement simulation ---

TEST(TimingControlSimulation, WaitStatementBlocksUntilTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    done = 0;\n"
      "    x = 0;\n"
      "    #10 done = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(done) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 99u}});
}

TEST(TimingControlSimulation, WaitStatementAlreadyTrue) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait(1) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 55u);
}

TEST(TimingControlSimulation, WaitStatementNullBody) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait(1) ;\n"
      "    x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

// --- jump_statement simulation ---

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

// --- delay_or_event_control (intra-assignment) simulation ---

TEST(TimingControlSimulation, IntraAssignDelayBlockingEvaluatesRhsFirst) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 10u);
}

TEST(TimingControlSimulation, IntraAssignDelayNonblocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd20;\n"
      "    a <= #1 b;\n"
      "    #5 ;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 20u}});
}

// --- Ordering of delay and concurrent processes ---

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

// --- Multiple edges in event expression ---

TEST(TimingControlSimulation, EventControlMultipleEdges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst, x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    rst = 0;\n"
      "    x = 0;\n"
      "    #5 rst = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk or posedge rst) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

}  // namespace
