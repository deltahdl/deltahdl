#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AssertionClockSim, ClockVariesFromOneAssertionToAnother) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk1;\n"
      "  logic clk2;\n"
      "  int hits1 = 0;\n"
      "  int hits2 = 0;\n"
      "  assert property (@(posedge clk1) 1'b1) hits1 = hits1 + 1;\n"
      "  assert property (@(posedge clk2) 1'b1) hits2 = hits2 + 1;\n"
      "  initial begin\n"
      "    clk1 = 0;\n"
      "    clk2 = 0;\n"
      "    #5 clk1 = 1;\n"
      "    #5 clk1 = 0;\n"
      "    #5 clk2 = 1;\n"
      "    #5 clk1 = 1;\n"
      "    #5 clk1 = 0;\n"
      "    #5 clk2 = 0;\n"
      "    #5 clk2 = 1;\n"
      "    #5 clk1 = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* hits1 = f.ctx.FindVariable("hits1");
  ASSERT_NE(hits1, nullptr);
  EXPECT_EQ(hits1->value.ToUint64(), 3u);
  auto* hits2 = f.ctx.FindVariable("hits2");
  ASSERT_NE(hits2, nullptr);
  EXPECT_EQ(hits2->value.ToUint64(), 2u);
}

TEST(AssertionClockSim, GatedClockSkipsTheTicksItsGateSuppresses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk iff en) 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    en = 1;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 en = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 en = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(AssertionClockSim, GlobalClockClocksTheAssertionAtTheGlobalClockingEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  assert property (@$global_clock 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(AssertionClockSim, GlobalClockFollowsTheDeclaredEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "  assert property (@$global_clock 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(AssertionClockSim, OperandRisingInTheTicksTimeStepIsStillSampledLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  int held = 0;\n"
      "  int broken = 0;\n"
      "  assert property (@(posedge clk) req) held = held + 1;\n"
      "  else broken = broken + 1;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    req = 1'b0;\n"
      "    #5 req = 1'b1; clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* held = f.ctx.FindVariable("held");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 0u);
  auto* broken = f.ctx.FindVariable("broken");
  ASSERT_NE(broken, nullptr);
  EXPECT_EQ(broken->value.ToUint64(), 1u);
}

TEST(AssertionClockSim,
     ClockVariableReadsCurrentInTheEventAndSampledInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int sampled_low = 0;\n"
      "  int sampled_high = 0;\n"
      "  assert property (@(posedge clk) clk == 1'b0)\n"
      "    sampled_low = sampled_low + 1;\n"
      "  else sampled_high = sampled_high + 1;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* sampled_low = f.ctx.FindVariable("sampled_low");
  ASSERT_NE(sampled_low, nullptr);
  EXPECT_EQ(sampled_low->value.ToUint64(), 1u);
  auto* sampled_high = f.ctx.FindVariable("sampled_high");
  ASSERT_NE(sampled_high, nullptr);
  EXPECT_EQ(sampled_high->value.ToUint64(), 0u);
}

TEST(AssertionClockSim, ActionBlockPercentMNamesTheAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic clk = 0;\n"
      "  base_rule1: assert property (@(posedge clk) 1'b1)\n"
      "    $display(\"%m, passing\");\n"
      "  else\n"
      "    $display(\"%m, failed\");\n"
      "  initial #1 clk = 1;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "m.base_rule1, passing\n");
}

TEST(AssertionClockSim, ASequenceClocksTheAssertionAtItsEndPoints) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic clk = 0, mycond = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  sequence seq1;\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "  C2: cover property (@seq1 mycond) $display(\"C2 %0t\", $time);\n"
      "  initial #30 $finish;\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("C2 5\nC2 15\nC2 25\n"), std::string::npos);
}

}  // namespace
