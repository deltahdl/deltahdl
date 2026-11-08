#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string AssumeSource(const std::string& statements) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0, gnt = 0, rst = 0;\n"
         "  logic ack = 0, reset_n = 0;\n"
         "  logic x = 1;\n"
         "  int v = 0;\n"
         "  int passes = 0, fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  property abc(a, b, c);\n"
         "    disable iff (c) @(posedge clk) a |=> b;\n"
         "  endproperty\n" +
         statements +
         "  initial begin\n"
         "    #10 reset_n = 1; req = 1;\n"
         "    #10 gnt = 1;\n"
         "    #10 ack = 1; v = 1;\n"
         "    #10 req = 0; gnt = 0; ack = 0;\n"
         "    #10 req = 1; ack = 1;\n"
         "    #10 req = 0; ack = 0; x = 0;\n"
         "    #2 rst = 1;\n"
         "    #6 rst = 0;\n"
         "    #2 x = 1; ack = 1;\n"
         "    #10 ack = 0; v = 2;\n"
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(AssumeStatementRun,
     PassAndFailStatementsFollowTheVerdictAndDisabledAttemptsRunNeither) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssumeSource("  counted: assume property (abc(req, gnt, rst))\n"
                   "    passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(AssumeStatementRun, WithoutAnElseClauseTheToolReportsTheFailedAssumption) {
  SimFixture f;
  std::string out = RunCapture(
      AssumeSource("  null_stmt: assume property (@(posedge clk) x) ;\n"), f);
  EXPECT_EQ(out, "$finish at time 90\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

TEST(AssumeStatementRun, AnAssumedDistHoldsForTheDistributionsValues) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssumeSource(
          "  a1: assume property (@(posedge clk) v dist {0:=40, 1:=60})\n"
          "    passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 8u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(AssumeStatementRun, AnAssertedDistIsTheInsideOperator) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssumeSource(
          "  int inside_passes = 0, inside_fails = 0;\n"
          "  dist_assert: assert property (@(posedge clk) v dist {0:=40, "
          "1:=60})\n"
          "    passes++; else fails++;\n"
          "  inside_assert: assert property (@(posedge clk) v inside {0, 1})\n"
          "    inside_passes++; else inside_fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 8u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("inside_passes")->value.ToUint64(), 8u);
  EXPECT_EQ(f.ctx.FindVariable("inside_fails")->value.ToUint64(), 1u);
}

TEST(AssumeStatementRun, AnAssertedDistWithADefaultItemHoldsForEveryValue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssumeSource(
          "  dist_assert: assert property (@(posedge clk) v dist {5:/1, "
          "default:/1})\n"
          "    passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

TEST(AssumeStatementRun, ACoveredDistIsTheInsideOperator) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(AssumeSource("  dist_cover: cover property (@(posedge clk) "
                                 "v dist {0:=40, 1:=60})\n"
                                 "    passes++;\n"),
                    f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 8u);
}

TEST(AssumeStatementRun, TheProtocolsAssumptionsHoldAndItsAssertionFails) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      AssumeSource("  property pr3;\n"
                   "    @(posedge clk) req |-> req[*1:$] ##0 ack;\n"
                   "  endproperty\n"
                   "  property pa1;\n"
                   "    @(posedge clk) !reset_n || !req |-> !ack;\n"
                   "  endproperty\n"
                   "  assume_req3: assume property (pr3) passes++;\n"
                   "  assert_ack1: assert property (pa1) else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(AssumeStatementRun, TheLabelOfAnInstanceAssertionNamesItsReport) {
  SimFixture f;
  std::string out = RunCapture(
      AssumeSource("  property pa1;\n"
                   "    @(posedge clk) !reset_n || !req |-> !ack;\n"
                   "  endproperty\n"
                   "  assert_ack1: assert property (pa1)\n"
                   "    else $display(\"%m failed at %0d\", $time);\n"),
      f);
  EXPECT_EQ(out, "t.assert_ack1 failed at 75\n$finish at time 90\n");
}

}  // namespace
