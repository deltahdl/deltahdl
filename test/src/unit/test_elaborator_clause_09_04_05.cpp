// §9.4.5

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(IntraAssignTimingElaboration, BlockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a = #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, NonblockingIntraDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial a <= #5 b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, BlockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, NonblockingIntraEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, RepeatEventBlockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IntraAssignTimingElaboration, RepeatEventNonblockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  initial q <= repeat(5) @(posedge clk) d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

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
      "    c = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10}, {"c", 99}});
}

TEST(IntraAssignTimingSimulation, NbaIntraAssignDelayCapturesRHS) {
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
      "    c = 8'd77;\n"
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
      "    #1 n = 100;\n"
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
  EXPECT_EQ(a->value.ToUint64(), 33u);
}

}  // namespace
