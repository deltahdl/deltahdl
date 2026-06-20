#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Section 9.4.5 — intra-assignment timing controls. The normative behaviour
// lives entirely at the simulation stage: the right-hand expression is
// evaluated when the assignment is encountered, the resulting value is held,
// and the write to the left-hand side is postponed by the intra-assignment
// delay or event control. These tests drive real source through the elaborator,
// lowerer, and scheduler so that the production execution path (stmt_exec.cpp /
// statement_assign_core.cpp) is the thing being observed.

// --- Right-hand side evaluated before the delay (blocking, delay form) ------

TEST(IntraAssignTimingSimulation, BlockingIntraDelayCapturesRhsBeforeDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a = #5 b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // The value of b at statement time (10) is captured even though b is later
  // mutated to 99 before the 5-tick delay elapses.
  EXPECT_EQ(a->value.ToUint64(), 10u);
}

TEST(IntraAssignTimingSimulation, BlockingIntraDelayPostponesWrite) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd44;\n"
      "    a = #5 b;\n"
      "    c = a;\n"  // runs only after the blocking delay; observes a == 44
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 44}, {"c", 44}});
}

// --- Right-hand side evaluated before the delay (nonblocking, delay form) ---

TEST(IntraAssignTimingSimulation, NbaIntraAssignDelay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd42;\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IntraAssignTimingSimulation, NbaIntraDelayDoesNotBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a <= #5 b;\n"
      "    c = 8'd99;\n"  // a nonblocking intra-delay does not stall the
                          // process
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10}, {"c", 99}});
}

TEST(IntraAssignTimingSimulation, NbaIntraAssignDelayCapturesRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'd10;\n"
      "    a <= #5 b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
}

// --- Right-hand side evaluated before the event control --------------------

TEST(IntraAssignTimingSimulation, BlockingIntraAssignEventCapturesRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd10;\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "    #3 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
}

TEST(IntraAssignTimingSimulation, BlockingIntraAssignEventBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd20;\n"
      "    a = @(posedge clk) b;\n"
      "    c = 8'd77;\n"  // blocked behind the event control
      "  end\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 20}, {"c", 77}});
}

TEST(IntraAssignTimingSimulation, NbaIntraAssignEventCapturesRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd30;\n"
      "    a <= @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 b = 8'd99;\n"
      "    #3 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 30u);
}

TEST(IntraAssignTimingSimulation, NbaIntraAssignEventDoesNotBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd15;\n"
      "    a <= @(posedge clk) b;\n"
      "    c = 8'd88;\n"
      "  end\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 15}, {"c", 88}});
}

// --- repeat event control: delay by N occurrences of the event -------------

TEST(IntraAssignTimingSimulation, BlockingRepeatEventWaitsNTimes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd50;\n"
      "    a = repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 50u);
}

TEST(IntraAssignTimingSimulation, BlockingRepeatEventCapturesRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd25;\n"
      "    a = repeat(2) @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 b = 8'd99;\n"
      "    #4 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // The right-hand side is sampled once, when the assignment is encountered.
  EXPECT_EQ(a->value.ToUint64(), 25u);
}

TEST(IntraAssignTimingSimulation, NbaRepeatEventWaitsNTimes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd60;\n"
      "    a <= repeat(2) @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 60u);
}

TEST(IntraAssignTimingSimulation, NbaRepeatEventDoesNotBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd40;\n"
      "    a <= repeat(2) @(posedge clk) b;\n"
      "    c = 8'd55;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 40}, {"c", 55}});
}

// --- repeat count evaluated once, before scheduling ------------------------

TEST(IntraAssignTimingSimulation, RepeatCountEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  int n;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    n = 2;\n"
      "    b = 8'd33;\n"
      "    a = repeat(n) @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 n = 100;\n"  // changing n after scheduling has no effect
      "    #4 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // Two posedges suffice because the count was fixed at 2 when encountered.
  EXPECT_EQ(a->value.ToUint64(), 33u);
}

// --- repeat count <= 0, unknown, or high-impedance => behave as no repeat ---

TEST(IntraAssignTimingSimulation, RepeatCountZeroBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd70;\n"
      "    a = repeat(0) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // No clock edge ever arrives; with count 0 the assignment occurs at once.
  EXPECT_EQ(a->value.ToUint64(), 70u);
}

TEST(IntraAssignTimingSimulation, RepeatCountNegativeBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  int n;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    n = -3;\n"
      "    b = 8'd80;\n"
      "    a = repeat(n) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 80u);
}

TEST(IntraAssignTimingSimulation, RepeatCountUnknownBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd90;\n"
      "    a = repeat(1'bx) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // An unknown count is treated as if there were no repeat construct.
  EXPECT_EQ(a->value.ToUint64(), 90u);
}

TEST(IntraAssignTimingSimulation, RepeatCountHighZBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd17;\n"
      "    a = repeat(1'bz) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // A high-impedance count is treated as if there were no repeat construct.
  EXPECT_EQ(a->value.ToUint64(), 17u);
}

// --- repeat over an OR event list: each operand counted separately ---------

TEST(IntraAssignTimingSimulation, RepeatCountsOrEdgesSeparatelyAtSameTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic phi1, phi2;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    phi1 = 0; phi2 = 1;\n"
      "    a = 8'd0;\n"
      "    b = 8'd44;\n"
      "    a = repeat(2) @(posedge phi1 or negedge phi2) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 phi1 = 1;\n"  // posedge phi1 and ...
      "    phi2 = 0;\n"  // ... negedge phi2 in the same time step => two events
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // Both edges at the same simulation time are counted, so the count of two is
  // reached and the held value is written. A single count would leave a at 0.
  EXPECT_EQ(a->value.ToUint64(), 44u);
}

TEST(IntraAssignTimingSimulation, RepeatCountsAcrossOrListOverTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x, y;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    x = 0; y = 0;\n"
      "    a = 8'd0;\n"
      "    b = 8'd66;\n"
      "    a = repeat(2) @(posedge x or posedge y) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 x = 1;\n"  // first occurrence
      "    #5 y = 1;\n"  // second occurrence, different signal, later time
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 66u);
}

// --- nonblocking repeat bypass: ≤0 / unknown / high-Z count, no repeat ------
// These exercise the dedicated count==0 branch on the nonblocking path, which
// is distinct from the blocking repeat path covered above.

TEST(IntraAssignTimingSimulation, NbaRepeatCountZeroBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    a = 8'd0;\n"
      "    b = 8'd70;\n"
      "    a <= repeat(0) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // No clock edge ever arrives; the nonblocking update is scheduled at once.
  EXPECT_EQ(a->value.ToUint64(), 70u);
}

TEST(IntraAssignTimingSimulation, NbaRepeatCountNegativeBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  int n;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    n = -3;\n"
      "    a = 8'd0;\n"
      "    b = 8'd80;\n"
      "    a <= repeat(n) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 80u);
}

TEST(IntraAssignTimingSimulation, NbaRepeatCountUnknownBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    a = 8'd0;\n"
      "    b = 8'd90;\n"
      "    a <= repeat(1'bx) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 90u);
}

TEST(IntraAssignTimingSimulation, NbaRepeatCountHighZBypasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    a = 8'd0;\n"
      "    b = 8'd17;\n"
      "    a <= repeat(1'bz) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 17u);
}

// --- nonblocking repeat samples its RHS once, when encountered -------------

TEST(IntraAssignTimingSimulation, NbaRepeatEventCapturesRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    b = 8'd25;\n"
      "    a <= repeat(2) @(posedge clk) b;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 b = 8'd99;\n"
      "    #4 clk = 1; #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // The value held is the one read when the statement executed (25), not the
  // later 99, even though the write is deferred until the second posedge.
  EXPECT_EQ(a->value.ToUint64(), 25u);
}

}  // namespace
