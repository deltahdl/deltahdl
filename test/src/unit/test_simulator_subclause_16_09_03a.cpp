#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/assertion.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(Assertion, ChangedDetected) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed", 5);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_changed", 7);
  EXPECT_EQ(r1, AssertionResult::kPass);
}

TEST(Assertion, ChangedStable) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_changed2";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_changed2", 42);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_changed2"));
  entry->cycle_count = 1;

  auto r1 = monitor.Evaluate("p_changed2", 42);
  EXPECT_EQ(r1, AssertionResult::kFail);
}

TEST(Assertion, RoseDetectsLowToHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose", 1), AssertionResult::kPass);
}

TEST(Assertion, RoseFalseWhenAlreadyHigh) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose2";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose2", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose2", 1), AssertionResult::kFail);
}

TEST(Assertion, FellDetectsHighToLow) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell", 0), AssertionResult::kPass);
}

TEST(Assertion, FellFalseWhenNotFalling) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell2";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell2", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell2"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell2", 0), AssertionResult::kFail);
}

TEST(Assertion, RoseFalseWhenLsbFalls) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose3";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose3", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose3", 0), AssertionResult::kFail);
}

TEST(Assertion, RoseIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_rose4";
  prop.kind = SvaPropertyKind::kRose;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_rose4", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_rose4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_rose4", 2), AssertionResult::kFail);
}

TEST(Assertion, FellFalseWhenLsbRises) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell3";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell3", 0);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell3"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell3", 1), AssertionResult::kFail);
}

TEST(Assertion, FellIgnoresHigherBitsWhenLsbUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_fell4";
  prop.kind = SvaPropertyKind::kFell;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_fell4", 1);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_fell4"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_fell4", 3), AssertionResult::kFail);
}

TEST(Assertion, StableTrueWhenUnchanged) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_stable";
  prop.kind = SvaPropertyKind::kStable;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  monitor.Evaluate("p_stable", 9);
  auto* entry = const_cast<AssertionEntry*>(monitor.FindEntry("p_stable"));
  entry->cycle_count = 1;

  EXPECT_EQ(monitor.Evaluate("p_stable", 9), AssertionResult::kPass);
  EXPECT_EQ(monitor.Evaluate("p_stable", 4), AssertionResult::kFail);
}

TEST(Assertion, FirstEvaluationHasNoPriorSample) {
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_first";
  prop.kind = SvaPropertyKind::kChanged;
  prop.signal_name = "sig";
  monitor.AddProperty(prop);

  EXPECT_EQ(monitor.Evaluate("p_first", 5), AssertionResult::kVacuousPass);
}

TEST(SampledValueSim, SampledReadsThePreponedValueOfItsArgument) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'h11;\n"
      "    #10;\n"
      "    x = 8'h22;\n"
      "    result = $sampled(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x11u);
}

TEST(SampledValueSim, RoseHoldsWhenTheLsbRisesBeforeTheEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic req = 0;\n"
      "  always @(posedge clk) assert property ($rose(req));\n"
      "  initial begin\n"
      "    #1 req = 1;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "");
}

TEST(SampledValueSim, RoseFailsWhenTheLsbDoesNotRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic req = 0;\n"
      "  always @(posedge clk) assert property ($rose(req));\n"
      "  initial #1 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(SampledValueSim, PastReturnsTheValueSampledAtThePreviousTick) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int x = 1;\n"
      "  int seen = 99;\n"
      "  always @(posedge clk) seen = $past(x);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    x = 2;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SampledValueSim, PastLooksBackTheStatedNumberOfTicks) {
  SimFixture f;
  auto* two_back = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int x = 1;\n"
      "  int two_back = 99;\n"
      "  int one_back = 99;\n"
      "  always @(posedge clk) begin\n"
      "    two_back = $past(x, 2);\n"
      "    one_back = $past(x);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; x = 2;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; x = 3;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "two_back");
  ASSERT_NE(two_back, nullptr);
  EXPECT_EQ(two_back->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("one_back")->value.ToUint64(), 2u);
}

TEST(SampledValueSim, PastGatedByExpression2SkipsTheTicksItIsLowAt) {
  SimFixture f;
  auto* seen = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic enable = 1;\n"
      "  int q = 1;\n"
      "  int seen = 99;\n"
      "  always @(posedge clk) seen = $past(q, 1, enable);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; q = 2; enable = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; q = 3; enable = 1;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 1u);
}

TEST(SampledValueSim, PastOfAnIndexedBitInALoopReadsThatBitsPast) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [3:0] b = 4'b0101;\n"
      "  logic [3:0] r = 4'b1111;\n"
      "  always @(posedge clk)\n"
      "    for (int i = 0; i < 4; i++) r[i] = $past(b[i]);\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0; b = 4'b1010;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0b0101u);
}

TEST(SampledValueExplicitClock, ProceduralValueChangeComparesTheClocksTicks) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic s = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    @(posedge clk); s = 1;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(s, @(posedge clk)));\n"
      "    @(posedge clk); s = 0;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(s, @(posedge clk)));\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT rose 0 fell 0\nOUT rose 0 fell 0\n");
}

TEST(SampledValueExplicitClock, ProceduralFellStableAndRoseAgree) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic s = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    @(posedge clk); s = 0;\n"
      "    @(posedge clk); #1;\n"
      "    $display(\"OUT fell %0d rose %0d stable %0d\", $fell(s, @(posedge "
      "clk)), $rose(s, @(posedge clk)), $stable(s, @(posedge clk)));\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT fell 0 rose 0 stable 1\n");
}

TEST(SampledValueExplicitClock, AnAssertionsFunctionSamplesAtItsOwnClock) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic clk2 = 0; initial begin #10; repeat (9) #10 clk2 = ~clk2; end\n"
      "  bit [0:9] rv = 10'b0101000000;\n"
      "  bit req; assign req = rv[0];\n"
      "  always @(negedge clk) rv <= rv << 1;\n"
      "  int c1 = 0, c2 = 0;\n"
      "  cover property (@(posedge clk) $rose(req)) c1++;\n"
      "  cover property (@(posedge clk) $rose(req, @(posedge clk2))) c2++;\n"
      "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c1=2 c2=1\n");
}

TEST(SampledValueExplicitClock, ThePriorPointIsTheClocksTickNotTheLastCall) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  logic s = 0, u = 1;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 2; i++) begin\n"
      "      #8 s = 1; u = 0;\n"
      "      #1 $display(\"OUT rose %0d fell %0d\", $rose(s, @(posedge clk)), "
      "$fell(u, @(posedge clk)));\n"
      "      #1 s = 0; u = 1;\n"
      "    end\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT rose 1 fell 1\nOUT rose 1 fell 1\n");
}

TEST(SampledValueExplicitClock, ChangedAndStableCompareTheClocksTick) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  logic s = 0;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 2; i++) begin\n"
      "      #8 s = 1;\n"
      "      #1 $display(\"OUT changed %0d stable %0d\", "
      "$changed(s, @(posedge clk)), $stable(s, @(posedge clk)));\n"
      "      #1 s = 0;\n"
      "    end\n"
      "    $finish(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "OUT changed 1 stable 0\nOUT changed 1 stable 0\n");
}

TEST(SampledValuePast, ThroughAVirtualInterfaceTheFirstTickIsTheDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "interface bus(input logic clk); logic [7:0] d; endinterface\n"
      "class Mon;\n"
      "  virtual bus vif;\n"
      "  function new(virtual bus v); vif = v; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic clk = 0; always #5 clk = ~clk;\n"
      "  bus b(clk);\n"
      "  virtual bus vif;\n"
      "  Mon m;\n"
      "  initial begin\n"
      "    vif = b; m = new(b);\n"
      "    b.d = 1;\n"
      "    @(negedge clk) b.d = 2;\n"
      "  end\n"
      "  always @(posedge clk)\n"
      "    $display(\"%0t v=%b c=%b\", $time, $past(vif.d), $past(m.vif.d));\n"
      "  initial #18 $finish;\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("5 v=xxxxxxxx c=xxxxxxxx\n15 v=00000001 c=00000001\n"),
            std::string::npos);
}

}  // namespace
