#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// Every buf/not truth-table row and every delay-selection rule of §28.5 is
// observed below by driving the full elaboration + simulation pipeline, so the
// rule is seen as produced by production code (the lowered continuous
// assignment plus the scheduler).

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

// Table 28-4 maps a high-impedance input of buf to an unknown output: a buf is
// not a pass-through of z, it drives x. The lowered buffer produces x for the z
// input through production evaluation.
TEST(BufNotSimulation, ProductionBufDrivesUnknownForHighImpedanceInput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  buf g(y, a);\n  initial a = 1'bz;\n");
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

// End-to-end over the instance-array syntax of §28.3.6: a buf array distributes
// one scalar buffer per bit, so each element applies the buf truth table to its
// own input bit. Driving a = 2'b10 yields y = 2'b10 (the high bit buffers 1,
// the low bit buffers 0), observed through the full elaborate + simulate
// pipeline.
TEST(BufNotSimulation, ProductionBufInstanceArrayBuffersPerBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [1:0] a;\n"
      "  wire [1:0] y;\n"
      "  buf b[1:0](y, a);\n"
      "  initial a = 2'b10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 0x3u, 0x2u);
  EXPECT_EQ(w.bval & 0x3u, 0x0u);
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

// Two delays: an output transition to x uses the smaller of the two delays,
// regardless of which slot holds it. Both delay orderings settle the x output
// at t=6 (input edge at t=3 plus the smaller delay 3), which distinguishes the
// min from either fixed slot: an "always rise" bug would give t=11 for #(8,3),
// and an "always fall" bug would give t=11 for #(3,8).
TEST(BufNotSimulation, ProductionTransitionToXUsesSmallerDelaySmallerFall) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(8, 3) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'bx; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 6u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

TEST(BufNotSimulation, ProductionTransitionToXUsesSmallerDelaySmallerRise) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(3, 8) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'bx; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 6u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

// The two-delay rise/fall selection must hold when the delays are supplied by a
// constant expression rather than an integer literal. Here both delays come
// from localparams; elaboration resolves the constant expressions and the
// scheduler still routes a falling not output through the second (fall) slot,
// so the input edge at t=3 settles the output one fall-delay (9) later at t=12.
TEST(BufNotSimulation, ProductionLocalparamTwoDelaysSelectFallSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam RISE = 4;\n"
      "  localparam FALL = 9;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  not #(RISE, FALL) g(y, a);\n"
      "  initial begin a = 1'b0; #3 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 12u);
}

// The same rule with the delays supplied by module parameters (their default
// values), which take the parameter-resolution path rather than the literal
// path. A rising buf output uses the first (rise) slot: input rises at t=3, so
// the output settles one rise-delay (4) later at t=7.
TEST(BufNotSimulation, ProductionParameterTwoDelaysSelectRiseSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter RISE = 4, parameter FALL = 9);\n"
      "  reg a;\n"
      "  wire y;\n"
      "  buf #(RISE, FALL) g(y, a);\n"
      "  initial begin a = 1'b0; #3 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
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

// The other half of "one delay specifies both rise and fall": the same single
// value also governs a rising output. A buf whose input rises at t=3 drives its
// output high one delay (5) later, settling at t=8 -- the same value the
// falling case above uses, confirming a lone delay is applied in both
// directions.
TEST(BufNotSimulation, ProductionSingleDelayAppliesToRisingOutput) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f, "  buf #5 g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 8u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 0u);
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
