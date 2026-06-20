#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(LogicGates, BufGateTruthTable) {
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kV0), Val4::kV0);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kV1), Val4::kV1);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNOutputGate(GateKind::kBuf, Val4::kZ), Val4::kX);
}

TEST(LogicGates, NotGateTruthTable) {
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kV0), Val4::kV1);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kV1), Val4::kV0);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kX), Val4::kX);
  EXPECT_EQ(EvalNOutputGate(GateKind::kNot, Val4::kZ), Val4::kX);
}

// §28.5: with two delays, the first determines the output rise delay and the
// second determines the output fall delay for a buf/not output transition.
TEST(LogicGates, TwoDelaysSelectRiseForRisingFallForFalling) {
  EXPECT_EQ(ComputeGateDelay(3, 8, Val4::kV0, Val4::kV1), 3u);
  EXPECT_EQ(ComputeGateDelay(3, 8, Val4::kV1, Val4::kV0), 8u);
}

// §28.5: with two delays, the smaller of the two applies to transitions to x.
TEST(LogicGates, TwoDelaysUseSmallerForTransitionToX) {
  EXPECT_EQ(ComputeGateDelay(3, 8, Val4::kV0, Val4::kX), 3u);
  EXPECT_EQ(ComputeGateDelay(8, 3, Val4::kV1, Val4::kX), 3u);
}

// §28.5: a single delay specifies both the rise delay and the fall delay, so
// every directional transition through the gate uses the same value.
TEST(LogicGates, SingleDelayAppliesToRiseAndFall) {
  EXPECT_EQ(ComputeGateDelay(6, 6, Val4::kV0, Val4::kV1), 6u);
  EXPECT_EQ(ComputeGateDelay(6, 6, Val4::kV1, Val4::kV0), 6u);
  EXPECT_EQ(ComputeGateDelay(6, 6, Val4::kV1, Val4::kX), 6u);
}

// §28.5: with no delay specification there is no propagation delay through the
// gate, so the output transition is scheduled with zero delay.
TEST(LogicGates, NoDelaySpecificationGivesZeroPropagationDelay) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV1, Val4::kX), 0u);
}

// The tests above observe the stage helpers directly. The following drive the
// full elaboration + simulation pipeline, so the buf/not truth table (Table
// 28-4) and the two-delay rise/fall selection are observed as produced by
// production code (the lowered continuous assignment plus the scheduler),
// rather than by the reference helper.

// Low bit of the resolved 4-state value of a 1-bit net after simulation.
// aval/bval encode: 0 -> (0,0), 1 -> (1,0), x -> (1,1), z -> (0,1).
struct ResolvedBit {
  uint64_t aval;
  uint64_t bval;
};

static ResolvedBit ReadResolvedBit(SimFixture& f, std::string_view name) {
  auto* net = f.ctx.FindNet(name);
  if (!net || !net->resolved) return {2u, 2u};
  const auto& w = net->resolved->value.words[0];
  return {w.aval & 1u, w.bval & 1u};
}

static RtlirDesign* ElaborateBufNot(SimFixture& f, const std::string& body) {
  return ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n" +
          body + "endmodule\n",
      f);
}

TEST(BufNotSimulation, ProductionBufPassesZeroToOutput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  buf g(y, a);\n  initial a = 1'b0;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 0u);
  EXPECT_EQ(b.bval, 0u);
}

TEST(BufNotSimulation, ProductionBufPassesOneToOutput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  buf g(y, a);\n  initial a = 1'b1;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 0u);
}

TEST(BufNotSimulation, ProductionBufDrivesUnknownForUnknownInput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  buf g(y, a);\n  initial a = 1'bx;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

TEST(BufNotSimulation, ProductionNotInvertsZeroToOne) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  not g(y, a);\n  initial a = 1'b0;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 0u);
}

TEST(BufNotSimulation, ProductionNotInvertsOneToZero) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  not g(y, a);\n  initial a = 1'b1;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 0u);
  EXPECT_EQ(b.bval, 0u);
}

TEST(BufNotSimulation, ProductionNotDrivesUnknownForUnknownInput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  not g(y, a);\n  initial a = 1'bx;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

// Table 28-4 maps a high-impedance input of not to an unknown output; the
// lowered inverter produces x for the z input through production evaluation.
TEST(BufNotSimulation, ProductionNotDrivesUnknownForHighImpedanceInput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  not g(y, a);\n  initial a = 1'bz;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

// Two delays: the first slot governs a rising output. A buf whose input rises
// at t=3 drives its output high one rise-delay (4) later, so the last
// scheduled activity is at t=7.
TEST(BufNotSimulation, ProductionBufRisingOutputUsesFirstDelaySlot) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(4, 9) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

// Two delays: the second slot governs a falling output. A not whose input
// rises at t=3 drives its output low one fall-delay (9) later, so the last
// scheduled activity is at t=12 -- distinct from the rise case above.
TEST(BufNotSimulation, ProductionNotFallingOutputUsesSecondDelaySlot) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  not #(4, 9) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 12u);
}

// One delay specifies both the rise and the fall delay. With only a single
// value, a falling not output is delayed by that same value (no distinct
// second slot exists), so the input edge at t=3 settles the output at t=8.
TEST(BufNotSimulation, ProductionSingleDelayAppliesToFallingOutput) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f, "  not #5 g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 8u);
}

// No delay specification: there is no propagation delay through the gate, so an
// input edge at t=3 produces the output change in the same time step. The last
// scheduled activity stays at t=3 rather than being pushed past it.
TEST(BufNotSimulation, ProductionNoDelaySpecHasZeroPropagationDelay) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f, "  buf g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 3u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 0u);
}

}  // namespace
