#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around the clause's property abc and the statements given, as
// test/src/e2e/assume_statement.sv is: clk rises at 5, 15, ..., 85; req is
// high at 15, 25 and 35 and gnt at 25 and 35, so the attempt of 35 fails at
// 45; req is high at 55 and rst across 65, so the attempts of 55 and 65
// are disabled; ack is high at 35, 55 and 75, reset_n low at 5 only, x
// low at 65 only, and v is 0, then 1 from 30 and 2 at 85; the run ends at
// 90.
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

// §16.14.2: an assumed property is checked as an asserted one is, the
// pass statements running where it is true, the fail statements where it
// is false, and neither where the evaluation is disabled: the attempt of
// 35 fails at 45, and the attempts of 55 and 65 are disabled.
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

// §16.14.2: with a null statement for the action and no else clause, the
// tool calls $error where the assumption fails, once, at 65.
TEST(AssumeStatementRun, WithoutAnElseClauseTheToolReportsTheFailedAssumption) {
  SimFixture f;
  std::string out = RunCapture(
      AssumeSource("  null_stmt: assume property (@(posedge clk) x) ;\n"), f);
  EXPECT_EQ(out, "$finish at time 90\n");
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
}

// §16.14.2: the property an assume statement assumes holds the same with
// or without its biasing, so the clause's a1, v dist {0:=40, 1:=60}, holds
// where v is 0 or 1 and fails where v is 2, at 85.
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

// §16.14.2: within an assert statement a dist is the inside operator with
// the weights ignored, so v dist {0:=40, 1:=60} asserted counts what v
// inside {0, 1} does.
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

// §16.14.2: within a cover statement a dist is the inside operator as
// well, so v dist {0:=40, 1:=60} is covered at the eight ticks v is 0 or 1.
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

// §16.14.2: the clause's protocol, req raised and held until ack and both
// dropped the cycle after: pr3, req |-> req[*1:$] ##0 ack, holds at every
// tick, the attempts of 15, 25 and 35 matching at 35 and that of 55 at 55,
// and pa1 fails at 75, where ack is raised with req low.
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

}  // namespace
