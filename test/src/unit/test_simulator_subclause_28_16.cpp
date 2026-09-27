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

// §10.3.3: a delay written on a net declaration that assigns nothing is a net
// delay, and "any value change that is to be applied to [the net] by some other
// statement shall be delayed" by it before it takes effect. Runs a module whose
// net `w` carries a declaration delay of five and is driven by `driver` alone,
// with the value that driver reads rising at t=100, and returns the time the
// run settles at. The two cases using it differ in nothing but that driver, so
// the module they share is written once here.
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

TEST(GateNetDelays, ProductionNetDelayDelaysSeparateContinuousAssignment) {
  // §10.3.3 names this arrangement and rules on it: "Specifying the delay in a
  // continuous assignment that is part of the net declaration shall be treated
  // differently from specifying a net delay and then making a continuous
  // assignment to the net." The declaration `wire #5 w;` assigns nothing, so
  // its delay is a net delay, and every value change another statement applies
  // to `w` waits five ticks before it takes effect. The continuous assignment
  // drives `w` from a rise at t=100, so the run settles at 105. Every other net
  // delay case in this file writes the initializer form, whose delay belongs to
  // the assignment the declaration makes and reaches the net by a route this
  // source does not use.
  EXPECT_EQ(SettleTicksForNetDelayDriver("assign w = a;"), 105u);
}

TEST(GateNetDelays, ProductionNetDelayDelaysGatePrimitiveDriver) {
  // §28.16 defines a net delay as "the time it takes from any driver on the net
  // changing value to the time when the net value is updated and propagated
  // further", so which construct drives the net does not change the answer: a
  // gate primitive is a driver on `w` exactly as the continuous assignment
  // above is, and the same five ticks stand between its output changing and the
  // net carrying the change. The buf carries no delay of its own, so the five
  // ticks are the net's alone and this case rests on no rule about how a gate
  // delay and a net delay combine.
  EXPECT_EQ(SettleTicksForNetDelayDriver("buf g(w, a);"), 105u);
}

TEST(GateNetDelays, ProductionUndrivenDelayedNetAcquiresNoDriver) {
  // §28.16 gives a net delay its effect on "any driver on the net changing
  // value", so a declaration carrying a delay and no assignment declares a net
  // and creates nothing that drives it. Honouring the delay on a separately
  // written driver must not manufacture a driver where the source wrote none:
  // the module gains no continuous assignment, the lowered net gains no driver,
  // and the run has nothing to schedule.
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

// §10.3.3 states the addition as the rule a net delay is held to. Ruling on the
// declaration that carries its own continuous assignment it says "the delay is
// part of the continuous assignment and is not a net delay. Thus, it shall not
// be added to the delay of other drivers on the net" -- a "thus" that follows
// only where a delay that is a net delay is added to them. §28.16 gives the two
// consecutive segments of one path, the driver's from its inputs to its output
// and the net's from that output changing to the net updating, so the time from
// the one to the other is their sum.
//
// The driver's delay was kept and the net's discarded, so this settled at 102
// rather than 107. The two delays are 2 and 5 -- neither a multiple of the
// other, and their sum is neither -- so a run keeping one of them alone is told
// from a run adding them.
TEST(GateNetDelays, ProductionNetDelayIsAddedToAContinuousAssignmentsOwnDelay) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("assign #2 w = a;"), 107u);
}

// §28.16 makes the answer the same whichever construct drives the net, so a
// gate primitive carrying its own delay adds the net's exactly as the
// assignment above does. The gate's 3 is distinct from the assignment's 2, so
// this case is not the one above under another name.
TEST(GateNetDelays, ProductionNetDelayIsAddedToAGatePrimitivesOwnDelay) {
  EXPECT_EQ(SettleTicksForNetDelayDriver("buf #3 g(w, a);"), 108u);
}

// §29.2 makes a primitive instance's output terminal a driver on the net
// connected to it, and §28.16 gives a net delay to "any driver on the net", so
// the construct driving the net does not change the answer. A gate reaches the
// pass that gives a driver its net's delay because a gate is lowered to a
// continuous assignment; §29.8's instances stand in RtlirModule::udp_insts and
// reached it through nothing, so the same net was delayed for one driver and
// undelayed for the other.
//
// The primitive is declared beside the module because a UDP is a top-level
// declaration, so these two cases build their own source rather than sharing
// the helper above.
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
  // The instance carries no delay of its own, so the five ticks are the net's
  // alone and this case rests on no rule about how two delays combine.
  EXPECT_EQ(SettleTicksForUdpDriver("p u (w, a);"), 105u);
}

// §29.8 gives an instance a delay of its own, which is the primitive's
// propagation delay and not the net's, so the two are added as they are for
// every other driver. The instance's 3 and the net's 5 are neither a multiple
// of the other and their sum is neither, so a run keeping one alone is told
// from a run adding them.
TEST(GateNetDelays, ProductionNetDelayIsAddedToAUdpInstancesOwnDelay) {
  EXPECT_EQ(SettleTicksForUdpDriver("p #3 u (w, a);"), 108u);
}

// §27.5 puts the items of a selected generate block into the enclosing module,
// so a driver written in one is a driver on the net exactly as a driver written
// beside it is, and §28.16 makes no distinction between them. The pass that
// gives a driver its net's delay ran while a module's own items were being
// elaborated, and ProcessPendingGenerate appends a block's items after that, so
// a driver in a block reached it through nothing.
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

// The net declared in the block as well as the driver. Elaborator::ScopedName
// names such a net under the block's path while the driver keeps the bare name
// the source wrote, so matching the two by the bare name reached this net
// through nothing whatever order the passes ran in.
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

// §23.9 takes the innermost declaration of a name, so a driver inside the block
// takes the block's net and its delay of 7 rather than the module-level net's
// 5. Two nets of one name, and the delays differ, so a match that crossed the
// scope is told from one that does not.
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

// §27.5 leaves an unselected generate block unelaborated, so nothing of it
// reaches the module and the module-level net keeps the delay it was declared
// with. Without this, a pass that walked a block whatever its condition would
// give the driver the unselected block's net.
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

// §28.16 (printed page 856): a gate delay is "the signal propagation delay
// from any gate input to the gate output", and the input ports of the module
// holding the gate are its inputs like any net (§23.2.2). The parent writes the
// ports after time 0 under names of its own, `a` and `c` for the ports `a` and
// `b`, in one time step, and the gate's output follows 4 later.
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

// §28.16: a port change that leaves the gate's output where it is, `a` rising
// while `b` holds the and at 0, is still an input change, and the gate goes on
// following its ports afterwards: `b` rising a step later drives the output 1
// after the delay, and `b` falling drives it 0 again.
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

// §28.16 with §23.10: the delay may be a parameter of the module holding the
// gate, `and #(D)`, set by each instance's override -- 4 by position and 9 by
// name -- and each instance's output follows its ports after its own delay.
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

// §28.16 names net delays beside gate delays, and §10.3.3 gives a continuous
// assignment's delay the same inertial treatment: `assign #4 y = a & b` inside
// a module follows the module's input ports as the gate does.
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

// §23.2.2: an input port follows what the parent connects to it for as long
// as the run lasts, including after a change of the port has met a delayed
// gate's pending transition inside the instance: the port `b` goes on following
// `b` of the parent, and the gate's output with it. The change at 10 falls in
// the time slot the gate's x->0 of time 0 matures in, and §4.7 (printed page
// 69) lets the two be taken "in any order", so whether a 0 is seen at 10 is
// left open; the 1 by 20 and the 0 at 40 are not.
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

// §6.6 (printed page 91): a net's value "shall be determined by the values of
// its drivers", and it is z only "if no driver is connected". A delayed gate is
// connected from the start and has computed nothing until its first transition
// lands (§28.16, printed page 856), so its net reads x, at the gate's strong
// strength, until the delay elapses.
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

// §28.3 (printed page 829): the instances of one declaration "shall have the
// same drive strength and delay specification", and each of them drives its
// own net x until that delay has passed.
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

// §6.6 with §10.3.2: a delayed assignment to a select of a net drives x on the
// bits it selects until its delay has passed, and the bits it does not select
// stay undriven, z.
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

// §28.16's Table 28-9 has the third of three delays govern a transition to z,
// and §28.6 has a disabled bufif1 output z, so a bufif1 disabled from the start
// drives x until its turn-off delay of 6 passes and only then leaves its net
// undriven.
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

// §10.3.3 (printed page 250), whose scalar delays are "treated in the same
// way as for gate delays": "In situations where a right-hand operand changes
// before a previous change has had time to propagate to the left-hand side",
// the new value is evaluated, and "If this right-hand side value differs from
// the value currently scheduled to propagate to the left-hand side, then the
// currently scheduled propagation event is descheduled." An or #30 whose input
// rises at 15 has its 1 due at 45; the input falls again at 35, the 0 now
// evaluated differs from the pending 1, and the 1 is descheduled -- a 20-unit
// pulse is shorter than the 30-unit delay and never reaches the output, only
// the 0 landing, 30 after the fall.
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

}  // namespace
