#include <gtest/gtest.h>

#include <initializer_list>
#include <tuple>

#include "fixture_simulator.h"
#include "model_gate_logic.h"
#include "model_val4.h"

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
  static constexpr Val4 kVals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 from : kVals) {
    for (Val4 to : kVals) {
      EXPECT_EQ(ComputeGateDelay(0, 0, from, to), 0u);
    }
  }
}

TEST(NInputGateDelay, SingleDelayDrivesBothRiseAndFall) {
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV0, Val4::kV1), 8u);
  EXPECT_EQ(ComputeGateDelay(8, 8, Val4::kV1, Val4::kV0), 8u);
}

TEST(NInputGateDelay, TwoDelaysSplitRiseAndFall) {
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kV1), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kV0), 9u);
}

TEST(NInputGateDelay, TwoDelaysToXUsesSmaller) {
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(4, 9, Val4::kV1, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV0, Val4::kX), 4u);
  EXPECT_EQ(ComputeGateDelay(9, 4, Val4::kV1, Val4::kX), 4u);
}

TEST(LogicGates, ProductionAndGateOutputsConjunction) {
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

TEST(LogicGates, ProductionAndGateControllingZeroDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
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
  EXPECT_EQ(w.aval & 1u, 0u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionAndGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
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
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(LogicGates, ProductionOrGateControllingOneDominatesHighZInput) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
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
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(LogicGates, ProductionXorGateHighZInputYieldsUnknown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire b;\n"
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
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

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

TEST(NInputGateDelay, ProductionTwoDelayAndGateTransitionToXUsesSmallerSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(4, 9) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; #5 b = 1'bx; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 9u);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 1u);
}

TEST(NInputGateDelay, ProductionTwoDelayAndGateSchedulerEndsAtInputPlusRise) {
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

TEST(NInputGateSim, ASingleInputGateDrivesXForAZInput) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire i;\n"
      "  wire oa, oo, ox, on;\n"
      "  and g1 (oa, i);\n"
      "  or  g2 (oo, i);\n"
      "  xor g3 (ox, i);\n"
      "  nand g4 (on, i);\n"
      "  initial #1 $display(\"%b %b %b %b\", oa, oo, ox, on);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x x x x\n");
}

}  // namespace
