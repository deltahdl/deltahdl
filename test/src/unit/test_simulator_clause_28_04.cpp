#include <gtest/gtest.h>

#include <initializer_list>
#include <tuple>

#include "fixture_simulator.h"
#include "model_gate_logic.h"

using namespace delta;

using GateTruthEntry = std::tuple<Val4, Val4, Val4>;

static void RunGateTruthTable(GateKind kind,
                              std::initializer_list<GateTruthEntry> cases,
                              const char* label) {
  for (auto& [a, b, expected] : cases) {
    EXPECT_EQ(EvalNInputGate(kind, a, b), expected)
        << label << " a=" << static_cast<int>(a)
        << " b=" << static_cast<int>(b);
  }
}

namespace {

TEST(LogicGates, AndGateTruthTable) {
  RunGateTruthTable(GateKind::kAnd,
                    {

                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV0},
                        {Val4::kV0, Val4::kX, Val4::kV0},
                        {Val4::kV0, Val4::kZ, Val4::kV0},

                        {Val4::kV1, Val4::kV0, Val4::kV0},
                        {Val4::kV1, Val4::kV1, Val4::kV1},
                        {Val4::kV1, Val4::kX, Val4::kX},
                        {Val4::kV1, Val4::kZ, Val4::kX},

                        {Val4::kX, Val4::kV0, Val4::kV0},
                        {Val4::kX, Val4::kV1, Val4::kX},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},

                        {Val4::kZ, Val4::kV0, Val4::kV0},
                        {Val4::kZ, Val4::kV1, Val4::kX},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "And");
}

TEST(LogicGates, OrGateTruthTable) {
  RunGateTruthTable(GateKind::kOr,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV1},
                        {Val4::kV1, Val4::kX, Val4::kV1},
                        {Val4::kV1, Val4::kZ, Val4::kV1},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kV1},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kV1},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Or");
}

TEST(LogicGates, XorGateTruthTable) {
  RunGateTruthTable(GateKind::kXor,
                    {
                        {Val4::kV0, Val4::kV0, Val4::kV0},
                        {Val4::kV0, Val4::kV1, Val4::kV1},
                        {Val4::kV0, Val4::kX, Val4::kX},
                        {Val4::kV0, Val4::kZ, Val4::kX},
                        {Val4::kV1, Val4::kV0, Val4::kV1},
                        {Val4::kV1, Val4::kV1, Val4::kV0},
                        {Val4::kV1, Val4::kX, Val4::kX},
                        {Val4::kV1, Val4::kZ, Val4::kX},
                        {Val4::kX, Val4::kV0, Val4::kX},
                        {Val4::kX, Val4::kV1, Val4::kX},
                        {Val4::kX, Val4::kX, Val4::kX},
                        {Val4::kX, Val4::kZ, Val4::kX},
                        {Val4::kZ, Val4::kV0, Val4::kX},
                        {Val4::kZ, Val4::kV1, Val4::kX},
                        {Val4::kZ, Val4::kX, Val4::kX},
                        {Val4::kZ, Val4::kZ, Val4::kX},
                    },
                    "Xor");
}

TEST(LogicGates, NandIsInvertedAnd) {
  CheckInversion(GateKind::kAnd, GateKind::kNand);
}

TEST(LogicGates, NorIsInvertedOr) {
  CheckInversion(GateKind::kOr, GateKind::kNor);
}

TEST(LogicGates, XnorIsInvertedXor) {
  CheckInversion(GateKind::kXor, GateKind::kXnor);
}

TEST(NInputGateDelay, NoDelaySpecYieldsZeroPropagation) {
  // An n-input logic gate without a delay specification propagates with
  // zero delay; the production helper short-circuits when both rise and
  // fall slots are zero.
  static constexpr Val4 kVals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 from : kVals) {
    for (Val4 to : kVals) {
      EXPECT_EQ(ComputeGateDelay(0, 0, from, to), 0u);
    }
  }
}

TEST(NInputGateDelay, SingleDelayDrivesBothRiseAndFall) {
  // With a single delay slot, both 0->1 and 1->0 transitions use the same
  // value; the helper threads rise into the fall slot internally.
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV0, Val4::kV1), 8u);
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV1, Val4::kV0), 8u);
}

TEST(NInputGateDelay, TwoDelaysSplitRiseAndFall) {
  // Two-delay specifications: first slot governs 0->1 transitions, second
  // slot governs 1->0 transitions.
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kV1), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kV0), 9u);
}

TEST(NInputGateDelay, TwoDelaysToXUsesSmaller) {
  // Transitions to an unknown output use the lesser of the rise and fall
  // slots regardless of which slot is smaller.
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV1, Val4::kX), 4u);
}

TEST(LogicGates, ProductionAndGateOutputsConjunction) {
  // The production simulator drives the AND output to the logical conjunction
  // of its two inputs once both reach known logic levels.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b0; end\n"
      "  and g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionNandGateInvertsConjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  nand g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionOrGateOutputsDisjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b1; end\n"
      "  or g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionNorGateInvertsDisjunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b0; b = 1'b0; end\n"
      "  nor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXorGateOutputsParity) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b0; end\n"
      "  xor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXnorGateInvertsParity) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  xnor g(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

// §28.4 Table 28-3, x/z rows, observed on the production gate rather than the
// evaluation model: an AND gate whose second input is an undriven wire (z)
// still resolves to 0 when the other input holds the controlling value 0.
TEST(LogicGates, ProductionAndGateControllingZeroDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"  // undriven -> high impedance (z)
      "  wire y;\n"
      "  and g(y, a, b);\n"
      "  initial a = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 0u);  // logic 0
  EXPECT_EQ(w.bval & 1u, 0u);
}

// §28.4 Table 28-3: a non-controlling input paired with z drives the AND output
// to x (the gate normalizes z to x, then 1 & x = x).
TEST(LogicGates, ProductionAndGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"  // undriven -> z
      "  wire y;\n"
      "  and g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(w.bval & 1u, 1u);
}

// §28.4 Table 28-3, or column: the OR gate's controlling value 1 dominates a z
// input on the production gate.
TEST(LogicGates, ProductionOrGateControllingOneDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"  // undriven -> z
      "  wire y;\n"
      "  or g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // logic 1
  EXPECT_EQ(w.bval & 1u, 0u);
}

// §28.4 Table 28-3, xor column: unlike AND/OR there is no controlling value —
// any x or z on an input forces the XOR output to x. Observed on the production
// gate with an undriven (z) second input.
TEST(LogicGates, ProductionXorGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"  // undriven -> z
      "  wire y;\n"
      "  xor g(y, a, b);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(w.bval & 1u, 1u);
}

// §28.4: with two delays the second value governs the output fall delay. A
// two-input AND holding 1 falls to 0 when an input drops; the falling edge
// scheduled at t=3 completes at 3 + fall(9) = 12 on the production scheduler.
TEST(NInputGateDelay, ProductionTwoDelayAndGateFallTransitionUsesSecondSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; #3 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 12u);
}

// §28.4: the smaller of the two delays applies to output transitions to x. The
// AND output at 1 goes to x when an input becomes x at t=3; the transition
// completes at 3 + min(4, 9) = 7, and the output settles to x.
TEST(NInputGateDelay, ProductionTwoDelayAndGateTransitionToXUsesSmallerSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; #3 b = 1'bx; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(NInputGateDelay, ProductionTwoDelayAndGateSchedulerEndsAtInputPlusRise) {
  // The two-delay form on a multi-input AND gate: a 0->1 input transition
  // routes through the first slot, observable through scheduler.CurrentTime.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b0; b = 1'b0; #3 a = 1'b1; b = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

}  // namespace
