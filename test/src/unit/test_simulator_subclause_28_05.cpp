#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(BufNotSimulation, ProductionNotDrivesUnknownForHighImpedanceInput) {
  SimFixture f;
  auto* design = ElaborateBufNot(f, "  not g(y, a);\n  initial a = 1'bz;\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

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

TEST(BufNotSimulation, ProductionBufRisingOutputUsesFirstDelaySlot) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(4, 9) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

TEST(BufNotSimulation, ProductionNotFallingOutputUsesSecondDelaySlot) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  not #(4, 9) g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 12u);
}

TEST(BufNotSimulation, ProductionTransitionToXUsesSmallerDelaySmallerFall) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(8, 3) g(y, a);\n  initial begin a = 1'b0; #10 a = 1'bx; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 13u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

TEST(BufNotSimulation, ProductionTransitionToXUsesSmallerDelaySmallerRise) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f,
      "  buf #(3, 8) g(y, a);\n  initial begin a = 1'b0; #10 a = 1'bx; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 13u);
  auto b = ReadResolvedBit(f, "y");
  EXPECT_EQ(b.aval, 1u);
  EXPECT_EQ(b.bval, 1u);
}

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

TEST(BufNotSimulation, ProductionSingleDelayAppliesToFallingOutput) {
  SimFixture f;
  auto* design = ElaborateBufNot(
      f, "  not #5 g(y, a);\n  initial begin a = 1'b0; #3 a = 1'b1; end\n");
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 8u);
}

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
