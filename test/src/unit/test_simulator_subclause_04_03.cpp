#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EventSimulationSim, SameValueVariableWriteIsNotAnUpdateEvent) {
  SimFixture f;
  auto* changes = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int changes;\n"
      "  initial changes = 0;\n"
      "  always @(a) changes = changes + 1;\n"
      "  initial begin\n"
      "    #1 a = 8'd5;\n"
      "    #1 a = 8'd5;\n"
      "    #1 a = 8'd9;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "changes");
  ASSERT_NE(changes, nullptr);
  EXPECT_EQ(changes->value.ToUint64(), 2u);
}

TEST(EventSimulationSim, VariableStateChangePropagatesToSensitiveProcess) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  always @(a) b = a;\n"
      "  initial begin\n"
      "    a = 8'd0; b = 8'd0;\n"
      "    #1 a = 8'd42;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(EventSimulationSim, NetStateChangeIsAlsoAnUpdateEvent) {
  SimFixture f;
  auto* seen = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  wire [7:0] y;\n"
      "  int seen;\n"
      "  assign y = a;\n"
      "  initial seen = 0;\n"
      "  always @(y) seen = seen + 1;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #1 a = 8'd7;\n"
      "    #1 a = 8'd7;\n"
      "    #1 a = 8'd9;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 3u);
}

TEST(EventSimulationSim, AllProcessesSensitiveToAnUpdateEventAreEvaluated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int c1, c2;\n"
      "  initial begin c1 = 0; c2 = 0; end\n"
      "  always @(a) c1 = c1 + 1;\n"
      "  always @(a) c2 = c2 + 10;\n"
      "  initial begin\n"
      "    #1 a = 8'd4;\n"
      "    #1 a = 8'd9;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* c1 = f.ctx.FindVariable("c1");
  auto* c2 = f.ctx.FindVariable("c2");
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  EXPECT_EQ(c1->value.ToUint64(), 2u);
  EXPECT_EQ(c2->value.ToUint64(), 20u);
}

TEST(EventSimulationSim, ProcessNotSensitiveToTheChangedSignalIsNotEvaluated) {
  SimFixture f;
  auto* cnt = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  int cnt;\n"
      "  initial cnt = 0;\n"
      "  always @(b) cnt = cnt + 1;\n"
      "  initial begin\n"
      "    #1 a = 8'd5;\n"
      "    #1 a = 8'd6;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(cnt, nullptr);
  EXPECT_EQ(cnt->value.ToUint64(), 0u);
}

TEST(EventSimulationSim, AlwaysCombProcessRespondsToAnInputUpdateEvent) {
  SimFixture f;
  auto* outv = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] in;\n"
      "  logic [7:0] outv;\n"
      "  always_comb outv = in + 8'd1;\n"
      "  initial begin\n"
      "    in = 8'd10;\n"
      "    #1 in = 8'd20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "outv");
  ASSERT_NE(outv, nullptr);
  EXPECT_EQ(outv->value.ToUint64(), 21u);
}

std::string RunStimulus(const std::string& process) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0, en = 0, d = 0;\n"
      "  wire y;\n"
      "  logic q;\n" +
          process +
          "  initial begin\n"
          "    #1 d = 1;\n"
          "    #1 en = 1;\n"
          "    #1 clk = 1;\n"
          "    #1 d = 0;\n"
          "  end\n"
          "  initial #10 $finish;\n"
          "endmodule\n",
      f);
}

TEST(EventSimulationSim, GatePrimitiveRespondsToAnInputUpdateEvent) {
  EXPECT_EQ(
      RunStimulus(
          "  buf g(y, d);\n"
          "  always @(y) if ($time > 0) $display(\"%0t y=%b\", $time, y);\n"),
      "1 y=1\n4 y=0\n$finish at time 10\n");
}

TEST(EventSimulationSim, UserDefinedPrimitiveRespondsToAnInputUpdateEvent) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "primitive pass(output o, input i);\n"
          "  table\n"
          "    0 : 0;\n"
          "    1 : 1;\n"
          "  endtable\n"
          "endprimitive\n"
          "module t;\n"
          "  logic d = 0;\n"
          "  wire y;\n"
          "  pass u(y, d);\n"
          "  always @(y) if ($time > 0) $display(\"%0t y=%b\", $time, y);\n"
          "  initial begin\n"
          "    #1 d = 1;\n"
          "    #1 d = 0;\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 y=1\n2 y=0\n");
}

TEST(EventSimulationSim, AlwaysLatchRespondsToAnInputUpdateEvent) {
  EXPECT_EQ(
      RunStimulus(
          "  always_latch if (en) q = d;\n"
          "  always @(q) if ($time > 0) $display(\"%0t q=%b\", $time, q);\n"),
      "2 q=1\n4 q=0\n$finish at time 10\n");
}

TEST(EventSimulationSim, AlwaysFfRespondsToItsClockUpdateEvent) {
  EXPECT_EQ(
      RunStimulus(
          "  always_ff @(posedge clk) q <= d;\n"
          "  always @(q) if ($time > 0) $display(\"%0t q=%b\", $time, q);\n"),
      "3 q=1\n$finish at time 10\n");
}

TEST(EventSimulationSim, ContinuousAssignmentRespondsToAnOperandUpdateEvent) {
  EXPECT_EQ(
      RunStimulus(
          "  assign y = d & en;\n"
          "  always @(y) if ($time > 0) $display(\"%0t y=%b\", $time, y);\n"),
      "2 y=1\n4 y=0\n$finish at time 10\n");
}

TEST(EventSimulationSim, ProceduralContinuousAssignmentRespondsToAnUpdate) {
  EXPECT_EQ(
      RunStimulus(
          "  initial assign q = d;\n"
          "  always @(q) if ($time > 0) $display(\"%0t q=%b\", $time, q);\n"),
      "1 q=1\n4 q=0\n$finish at time 10\n");
}

TEST(EventSimulationSim, ForcedValueRespondsToAnOperandUpdateEvent) {
  EXPECT_EQ(
      RunStimulus(
          "  initial force q = d | clk;\n"
          "  always @(q) if ($time > 0) $display(\"%0t q=%b\", $time, q);\n"),
      "1 q=1\n$finish at time 10\n");
}

TEST(EventSimulationSim, SpawnedTaskRespondsToAnUpdateEvent) {
  EXPECT_EQ(RunStimulus("  task automatic watch();\n"
                        "    @(en) $display(\"%0t en=%b\", $time, en);\n"
                        "  endtask\n"
                        "  initial fork watch(); join_none\n"),
            "2 en=1\n$finish at time 10\n");
}

}  // namespace
