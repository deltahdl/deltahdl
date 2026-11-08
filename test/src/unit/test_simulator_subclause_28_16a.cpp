#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

static uint64_t SettleTicks(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src.c_str(), f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  LowerAndRun(design, f);
  return f.scheduler.CurrentTime().ticks;
}

static uint64_t SettleTicksForNetDelayDriver(const std::string& driver) {
  return SettleTicks(
      "module m;\n"
      "  reg a;\n"
      "  wire #5 w;\n"
      "  " +
      driver +
      "\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n");
}

TEST(GateNetDelays, ProductionNoDelaySchedulerStopsAtZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and g(y, a, a);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(GateNetDelays, ProductionRiseTransitionAdvancesByFirstSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'b0; #2 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 9u);
}

TEST(GateNetDelays, ProductionFallTransitionAdvancesBySecondSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'b1; #20 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 31u);
}

TEST(GateNetDelays, ProductionDelayedGateSettlesToInputConjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(3, 5) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(GateNetDelays, ProductionTransitionFromXToZeroUsesFallSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'bx; #100 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 111u);
}

TEST(GateNetDelays, ProductionTransitionFromXToOneUsesRiseSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'bx; #100 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionSingleDelayAppliesToRiseAndFall) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  and #(5) g(y, a, a);\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            105u);
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  and #(5) g(y, a, a);\n"
                        "  initial begin a = 1'b1; #100 a = 1'b0; end\n"
                        "endmodule\n"),
            105u);
}

TEST(GateNetDelays, ProductionTwoDelayTurnOffToHighZUsesLesserSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(7, 11) g(y, d, en);\n"
      "  initial begin d = 1'b1; en = 1'b1; #100 en = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionThreeDelayTurnOffToHighZUsesTurnOffSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(7, 11, 15) g(y, d, en);\n"
      "  initial begin d = 1'b1; en = 1'b1; #100 en = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 115u);
}

TEST(GateNetDelays, ProductionThreeDelayRiseUsesFirstSlotFallUsesSecond) {
  EXPECT_EQ(
      SettleTicks("module m;\n"
                  "  reg d, en;\n"
                  "  wire y;\n"
                  "  bufif1 #(7, 11, 15) g(y, d, en);\n"
                  "  initial begin en = 1'b1; d = 1'b0; #100 d = 1'b1; end\n"
                  "endmodule\n"),
      107u);
  EXPECT_EQ(
      SettleTicks("module m;\n"
                  "  reg d, en;\n"
                  "  wire y;\n"
                  "  bufif1 #(7, 11, 15) g(y, d, en);\n"
                  "  initial begin en = 1'b1; d = 1'b1; #100 d = 1'b0; end\n"
                  "endmodule\n"),
      111u);
}

TEST(GateNetDelays, ProductionThreeDelayToUnknownUsesSmallestSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(7, 11, 15) g(y, d, en);\n"
      "  initial begin d = 1'b0; en = 1'b1; #100 en = 1'bx; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionInputStrengthDoesNotAffectPropagationDelay) {
  auto settle_for = [](const char* strength) {
    return SettleTicks(std::string("module m;\n"
                                   "  reg drv;\n"
                                   "  wire a;\n"
                                   "  wire y;\n"
                                   "  assign ") +
                       strength +
                       " a = drv;\n"
                       "  and #(7, 11) g(y, a, a);\n"
                       "  initial begin drv = 1'b0; #100 drv = 1'b1; end\n"
                       "endmodule\n");
  };
  uint64_t strong = settle_for("(strong0, strong1)");
  uint64_t weak = settle_for("(weak0, weak1)");
  uint64_t pull = settle_for("(pull0, pull1)");
  EXPECT_EQ(strong, 107u);
  EXPECT_EQ(weak, 107u);
  EXPECT_EQ(pull, 107u);
}

TEST(GateNetDelays, ProductionTwoDelayToUnknownUsesLesserSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #(11, 15) g(y, d, en);\n"
      "  initial begin d = 1'b0; en = 1'b1; #100 en = 1'bx; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 111u);
}

TEST(GateNetDelays, ProductionNetDeclarationDelaySelectsSlotByTransition) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire #(7, 11) y = a;\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            107u);
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire #(7, 11) y = a;\n"
                        "  initial begin a = 1'b1; #100 a = 1'b0; end\n"
                        "endmodule\n"),
            111u);
}

TEST(GateNetDelays, ProductionSingleDelayAppliesToTurnOff) {
  EXPECT_EQ(
      SettleTicks("module m;\n"
                  "  reg d, en;\n"
                  "  wire y;\n"
                  "  bufif1 #(5) g(y, d, en);\n"
                  "  initial begin d = 1'b1; en = 1'b1; #100 en = 1'b0; end\n"
                  "endmodule\n"),
      105u);
}

TEST(GateNetDelays, ProductionTransitionFromHighZToZeroUsesFallSlot) {
  EXPECT_EQ(
      SettleTicks("module m;\n"
                  "  reg d, en;\n"
                  "  wire y;\n"
                  "  bufif1 #(7, 11) g(y, d, en);\n"
                  "  initial begin d = 1'b0; en = 1'b0; #100 en = 1'b1; end\n"
                  "endmodule\n"),
      111u);
}

TEST(GateNetDelays, ProductionTransitionFromHighZToOneUsesRiseSlot) {
  EXPECT_EQ(
      SettleTicks("module m;\n"
                  "  reg d, en;\n"
                  "  wire y;\n"
                  "  bufif1 #(7, 11) g(y, d, en);\n"
                  "  initial begin d = 1'b1; en = 1'b0; #100 en = 1'b1; end\n"
                  "endmodule\n"),
      107u);
}

TEST(GateNetDelays, ProductionBufGateDelaySelectsRiseAndFallSlots) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  buf #(7, 11) g(y, a);\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            107u);
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  buf #(7, 11) g(y, a);\n"
                        "  initial begin a = 1'b1; #100 a = 1'b0; end\n"
                        "endmodule\n"),
            111u);
}

TEST(GateNetDelays, ProductionNotGateDelaySelectsSlotByInvertedOutput) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  not #(7, 11) g(y, a);\n"
                        "  initial begin a = 1'b1; #100 a = 1'b0; end\n"
                        "endmodule\n"),
            107u);
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  not #(7, 11) g(y, a);\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            111u);
}

TEST(GateNetDelays, ProductionDelayValueFromConstantExpressionSelectsSlot) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  parameter RISE = 7;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  and #(RISE, 11) g(y, a, a);\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            107u);
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  localparam RISE = 7;\n"
                        "  reg a;\n"
                        "  wire y;\n"
                        "  and #(RISE, 11) g(y, a, a);\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            107u);
}

TEST(GateNetDelays, ProductionNetDelayDelaysSeparateContinuousAssignment) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("assign w = a;"), 105u);
}

TEST(GateNetDelays, ProductionNetDelayDelaysGatePrimitiveDriver) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("buf g(w, a);"), 105u);
}

TEST(GateNetDelays, ProductionUndrivenDelayedNetAcquiresNoDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire #5 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_TRUE(design->top_modules[0]->assigns.empty());
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->drivers.empty());
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(GateNetDelays, ProductionNetDelayIsAddedToAContinuousAssignmentsOwnDelay) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("assign #2 w = a;"), 107u);
}

TEST(GateNetDelays, ProductionNetDelayIsAddedToAGatePrimitivesOwnDelay) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("buf #3 g(w, a);"), 108u);
}

static uint64_t SettleTicksForUdpDriver(const std::string& inst) {
  return SettleTicks(
      "primitive p (out, in);\n"
      "  output out;\n"
      "  input in;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  reg a;\n"
      "  wire #5 w;\n"
      "  " +
      inst +
      "\n"
      "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
      "endmodule\n");
}

TEST(GateNetDelays, ProductionNetDelayDelaysAUdpInstanceDriver) {
  EXPECT_EQ(SettleTicksForUdpDriver("p u (w, a);"), 105u);
}

TEST(GateNetDelays, ProductionNetDelayIsAddedToAUdpInstancesOwnDelay) {
  EXPECT_EQ(SettleTicksForUdpDriver("p #3 u (w, a);"), 108u);
}

TEST(GateNetDelays, ProductionNetDelayReachesADriverInAGenerateBlock) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire #5 w;\n"
                        "  if (1) begin : b\n"
                        "    assign w = a;\n"
                        "  end\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            105u);
}

TEST(GateNetDelays, ProductionNetDelayReachesADriverInTheBlockThatDeclaredIt) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  if (1) begin : b\n"
                        "    wire #5 w;\n"
                        "    assign w = a;\n"
                        "  end\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            105u);
}

TEST(GateNetDelays, ProductionNetDelayTakesTheInnermostDeclarationOfTheName) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire #5 w;\n"
                        "  if (1) begin : b\n"
                        "    wire #7 w;\n"
                        "    assign w = a;\n"
                        "  end\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            107u);
}

TEST(GateNetDelays, ProductionNetDelayIgnoresAnUnselectedGenerateBlock) {
  EXPECT_EQ(SettleTicks("module m;\n"
                        "  reg a;\n"
                        "  wire #5 w;\n"
                        "  if (0) begin : b\n"
                        "    wire #7 w;\n"
                        "  end\n"
                        "  assign w = a;\n"
                        "  initial begin a = 1'b0; #100 a = 1'b1; end\n"
                        "endmodule\n"),
            105u);
}

TEST(GateNetDelays, DelayedGateFollowsInputPortsWrittenInOneStep) {
  SimFixture f;
  auto out = RunCapture(
      "module sub (output y, input a, b);\n"
      "  and #4 g (y, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  logic a = 0, c = 0;\n"
      "  sub s1 (y, a, c);\n"
      "  initial begin\n"
      "    #10 a = 1; c = 1;\n"
      "    #3 $display(\"t=%0t y=%b\", $time, y);\n"
      "    #2 $display(\"t=%0t y=%b\", $time, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=13 y=0\n"
            "t=15 y=1\n");
}

TEST(GateNetDelays, DelayedGateFollowsPortsAfterAnEvaluationThatHolds) {
  SimFixture f;
  auto out = RunCapture(
      "module sub (output y, input a, b);\n"
      "  and #4 g (y, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  logic a = 0, c = 0;\n"
      "  sub s1 (y, a, c);\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "    #1 c = 1;\n"
      "    #5 $display(\"t=%0t y=%b\", $time, y);\n"
      "    c = 0;\n"
      "    #5 $display(\"t=%0t y=%b\", $time, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=16 y=1\n"
            "t=21 y=0\n");
}

TEST(GateNetDelays, ParameterDelayOfASubmoduleGateFollowsItsPorts) {
  SimFixture f;
  auto out = RunCapture(
      "module sub #(parameter D = 2) (output y, input a, b);\n"
      "  and #(D) g (y, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  wire y, z;\n"
      "  logic a = 0;\n"
      "  sub #(4) s1 (y, a, a);\n"
      "  sub #(.D(9)) s2 (z, a, a);\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "    #3 $display(\"t=%0t y=%b z=%b\", $time, y, z);\n"
      "    #2 $display(\"t=%0t y=%b z=%b\", $time, y, z);\n"
      "    #5 $display(\"t=%0t y=%b z=%b\", $time, y, z);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=13 y=0 z=0\n"
            "t=15 y=1 z=0\n"
            "t=20 y=1 z=1\n");
}

TEST(GateNetDelays, DelayedAssignFollowsInputPorts) {
  SimFixture f;
  auto out = RunCapture(
      "module sub (output y, input a, b);\n"
      "  assign #4 y = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  wire y;\n"
      "  logic a = 0, c = 0;\n"
      "  sub s1 (y, a, c);\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "    #1 c = 1;\n"
      "    #10 $display(\"t=%0t y=%b\", $time, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t=21 y=1\n");
}

TEST(GateNetDelays, InputPortKeepsFollowingAfterItCancelsAPendingTransition) {
  SimFixture f;
  auto out = RunCapture(
      "module mycell(input a, input b, output w);\n"
      "  and #10 (w, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b; wire tw;\n"
      "  mycell u(.a(a), .b(b), .w(tw));\n"
      "  initial begin\n"
      "    a = 1; b = 0;\n"
      "    #10 b = 1;\n"
      "    #15 $display(\"t=%0t u.b=%b w=%b\", $time, u.b, tw);\n"
      "    #5 b = 0;\n"
      "    #5 $display(\"t=%0t u.b=%b w=%b\", $time, u.b, tw);\n"
      "    #10 $display(\"t=%0t u.b=%b w=%b\", $time, u.b, tw);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=25 u.b=1 w=1\n"
            "t=35 u.b=0 w=1\n"
            "t=45 u.b=0 w=0\n");
}

TEST(GateNetDelays, DelayedGateOutputIsUnknownUntilItsFirstTransition) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire y;\n"
      "  logic a = 1, b = 1;\n"
      "  and #4 g (y, a, b);\n"
      "  initial begin\n"
      "    #2 $display(\"t=%0t y=%b v=%v\", $time, y, y);\n"
      "    #2 $display(\"t=%0t y=%b v=%v\", $time, y, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=2 y=x v=StX\n"
            "t=4 y=1 v=St1\n");
}

TEST(GateNetDelays, GatesOfOneDeclarationEachDriveXUntilTheSharedDelay) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire y1, y2;\n"
      "  logic a = 1, b = 0;\n"
      "  or (strong1, weak0) #4 g1 (y1, a, b), g2 (y2, b, b);\n"
      "  initial begin\n"
      "    #3 $display(\"t=%0t y1=%b y2=%b\", $time, y1, y2);\n"
      "    #2 $display(\"t=%0t y1=%b y2=%b\", $time, y1, y2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=3 y1=x y2=x\n"
            "t=5 y1=1 y2=0\n");
}

TEST(GateNetDelays, DelayedSelectDriverIsUnknownOnItsBitsUntilItsDelay) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [3:0] w;\n"
      "  assign #5 w[2:1] = 2'b10;\n"
      "  initial begin\n"
      "    #1 $display(\"t=%0t w=%b\", $time, w);\n"
      "    #5 $display(\"t=%0t w=%b\", $time, w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=1 w=zxxz\n"
            "t=6 w=z10z\n");
}

TEST(GateNetDelays, DisabledThreeStateGateTurnsOffAfterItsTurnOffDelay) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire v;\n"
      "  bufif1 #(4, 4, 6) g (v, 1'b1, 1'b0);\n"
      "  initial begin\n"
      "    #5 $display(\"t=%0t v=%b %v\", $time, v, v);\n"
      "    #2 $display(\"t=%0t v=%b %v\", $time, v, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=5 v=x StX\n"
            "t=7 v=z HiZ\n");
}

TEST(GateNetDelays, PulseShorterThanTheGateDelayNeverReachesTheOutput) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  logic d; wire tq;\n"
      "  or #30 (tq, d, 1'b0);\n"
      "  always @(tq) if ($time > 0) $display(\"t=%0t q=%b\", $time, tq);\n"
      "  initial begin\n"
      "    d = 0;\n"
      "    #15 d = 1;\n"
      "    #20 d = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t=65 q=0\n");
}

TEST(GateNetDelays, AGatesDelayIsChosenFromItsOwnPreviousOutput) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg a = 1, b = 0;\n"
      "  wand w;\n"
      "  buf #(1, 10) g (w, a);\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    #20 a = 0;\n"
      "    #5 b = 1;\n"
      "    #2 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

}  // namespace
