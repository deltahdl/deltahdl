#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a self-contained module through elaboration and the lowered simulator,
// returning the time of the last scheduled event. Used by the production delay
// tests below to observe which slot of the gate's delay spec the scheduler
// charged for the transition under test.
static uint64_t SettleTicks(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src.c_str(), f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  LowerAndRun(design, f);
  return f.scheduler.CurrentTime().ticks;
}

TEST(GateNetDelays, ProductionNoDelaySchedulerStopsAtZero) {
  // Running the lowered simulator on a gate without a delay specification
  // leaves the scheduler at time zero: the production coroutine takes the
  // no-delay branch and never schedules a propagation event.
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
  // A 0->1 transition routes through the rise slot of the production
  // SelectContAssignDelay path; the scheduler's last event lands at the
  // input-change time plus the first delay slot.
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
  // A 1->0 transition (after the gate has stabilised at 1) routes through the
  // fall slot. The scheduler's last event lands at the input-change time plus
  // the second delay slot.
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
  // With a non-zero delay spec, the production simulator's coroutine still
  // converges the output to the AND of its inputs after the delay elapses.
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
  // After the gate stabilises at x, driving the input to 0 should route the
  // transition through the fall slot rather than the lesser of rise/fall.
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
  // First iter applies min(7,11)=7 to settle y at x by t=7. At t=100 the x->0
  // transition then schedules through the fall slot: 100 + 11 = 111.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 111u);
}

TEST(GateNetDelays, ProductionTransitionFromXToOneUsesRiseSlot) {
  // Symmetric to the previous test: a stabilised-x output transitioning to 1
  // should route through the rise slot.
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
  // x->1 routes through the rise slot: 100 + 7 = 107.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionSingleDelayAppliesToRiseAndFall) {
  // §28.16: when one delay value is given it is used for all propagation
  // delays. A gate with a single delay cannot distinguish rise from fall, so a
  // 0->1 and a 1->0 transition both settle exactly one delay after the input
  // change.
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
  // §28.16 / Table 28-9 (two-delay, to z): a bufif1 driven off transitions its
  // output to high impedance, which routes through the lesser of the rise and
  // fall slots because no separate turn-off slot is supplied.
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
  // The output settles at 1 by the rise slot, then the turn-off to z at t=100
  // routes through min(7, 11) = 7: 100 + 7 = 107.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionThreeDelayTurnOffToHighZUsesTurnOffSlot) {
  // §28.16 / Table 28-9 (three-delay, to z): the third delay is the turn-off
  // delay, charged when the output transitions to high impedance.
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
  // Turn-off to z at t=100 routes through the third (turn-off) slot: 100 + 15.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 115u);
}

TEST(GateNetDelays, ProductionThreeDelayRiseUsesFirstSlotFallUsesSecond) {
  // §28.16: for a three-delay spec the first delay is the transition to 1
  // (rise) and the second is the transition to 0 (fall), even with a turn-off
  // slot present. Each design ends on the transition under test so the last
  // scheduled event reveals the slot used.
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
  // §28.16: when a value changes to x the delay is the smallest of the three
  // delays. Driving the enable to x makes the bufif1 output ambiguous (x), and
  // the transition to x lands after min(rise, fall, turn-off).
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
  // Output settles at 0 by t=11 (fall), then the enable going x drives y to x
  // at t=100 + min(7, 11, 15) = 107.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

TEST(GateNetDelays, ProductionInputStrengthDoesNotAffectPropagationDelay) {
  // §28.16: the strength of the input signal shall not affect the propagation
  // delay from an input to an output. The gate input is driven through
  // continuous assignments of differing drive strength; the logic transition is
  // identical in every case, and the gate output settles at the same time.
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
  // 0->1 at t=100 routes through the rise slot: 100 + 7 = 107, independent of
  // the strength the input was driven with.
  EXPECT_EQ(strong, 107u);
  EXPECT_EQ(weak, 107u);
  EXPECT_EQ(pull, 107u);
}

TEST(GateNetDelays, ProductionTwoDelayToUnknownUsesLesserSlot) {
  // §28.16 / Table 28-9 (two-delay, to x): a change to the unknown value uses
  // the lesser of the two delays. This is the two-delay counterpart of the
  // three-delay min-of-all rule and exercises a distinct branch that never
  // consults a turn-off slot. The delays are chosen so the fall slot (15) is
  // larger than the rise slot (11): if a phantom third slot were consulted the
  // result would differ, so landing at min(11, 15) = 11 confirms only the two
  // present slots are considered.
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
  // Output settles at 0 by t=15 (fall), then the enable going x drives y to x
  // at t=100 + min(11, 15) = 111.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 111u);
}

TEST(GateNetDelays, ProductionNetDeclarationDelaySelectsSlotByTransition) {
  // §28.16: net delays (up to three per net) govern the driver-to-net
  // propagation just as gate delays do, and select the same Table 28-9 slots. A
  // net declaration assignment with a two-value delay drives its rise
  // transition through the first slot and its fall transition through the
  // second.
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
  // §28.16: a single delay value is used for every propagation delay, including
  // the transition to high impedance. A one-delay bufif1 driven off charges the
  // same single value it uses for rise and fall, since there is no distinct
  // turn-off slot to fall back to.
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
  // §28.16 / Table 28-9 (z -> 0 row): a driver returning a net from high
  // impedance to 0 routes through the fall slot. The bufif1 starts disabled so
  // its output holds z, then the data drives it to 0 once enabled.
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
  // §28.16 / Table 28-9 (z -> 1 row): a driver returning a net from high
  // impedance to 1 routes through the rise slot -- the from-z source selects
  // the slot by the destination value, mirroring the from-x rows.
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
  // §28.16 with a §28.5 buf gate as the delay carrier: the non-inverting buffer
  // passes its input, so an input rise drives an output rise (first slot) and
  // an input fall drives an output fall (second slot).
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
  // §28.16 with a §28.5 not gate: the inverting gate maps an input rise to an
  // output fall, so the slot chosen follows the output transition (rise slot
  // for the output going to 1, fall slot for the output going to 0), not the
  // input.
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
  // §28.16: the delay values that drive slot selection may be produced by a
  // parameter or localparam, not only a literal -- these resolve through a
  // different elaboration path than an integer literal but must yield the same
  // propagation delay. Both forms place the 0->1 rise transition at 100 + 7.
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

}  // namespace
