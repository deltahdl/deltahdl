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

constexpr const char* kBufNotLevels[] = {"1'b0", "1'b1", "1'bx", "1'bz"};

std::string EachInputShown(const std::string& decls,
                           const std::string& outputs) {
  std::string src = "module m;\n  logic i;\n";
  src += decls;
  src += "  initial begin\n";
  for (const char* level : kBufNotLevels) {
    src += "    i = ";
    src += level;
    src += "; #1 $write(\"";
    src += outputs;
    src += " \");\n";
  }
  src += "    $display;\n  end\nendmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

TEST(BufNotSimulation, EveryOutputOfAMultiOutputGateTakesTheTableValue) {
  EXPECT_EQ(EachInputShown("  wire o1, o2, o3;\n  buf b(o1, o2, o3, i);\n",
                           "%b%b%b\", o1, o2, o3, \""),
            "000 111 xxx xxx \n");
  EXPECT_EQ(EachInputShown("  wire o1, o2, o3;\n  not n(o1, o2, o3, i);\n",
                           "%b%b%b\", o1, o2, o3, \""),
            "111 000 xxx xxx \n");
}

TEST(BufNotSimulation, ANotInstanceArrayInvertsEachBit) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  wire [3:0] y;\n"
      "  not n[3:0](y, a);\n"
      "  initial begin a = 4'b10xz; #1 $display(\"%b\", y); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "01xx\n");
}

TEST(BufNotSimulation, AGateInAGenerateBlockDrivesTheTableValue) {
  EXPECT_EQ(EachInputShown("  wire [1:0] p, q;\n"
                           "  for (genvar k = 0; k < 2; k++) begin : g\n"
                           "    buf b(p[k], i);\n"
                           "    not n(q[k], i);\n"
                           "  end\n",
                           "%b%b\", p, q, \""),
            "0011 1100 xxxx xxxx \n");
  EXPECT_EQ(EachInputShown("  wire p, q;\n"
                           "  if (1) begin : c\n"
                           "    buf b(p, i);\n"
                           "    not n(q, i);\n"
                           "  end\n",
                           "%b%b\", p, q, \""),
            "01 10 xx xx \n");
}

std::string BufNotTransitionsShown(const std::string& gate,
                                   const std::string& delay) {
  std::string src = "module m;\n  logic a;\n  wire y;\n  ";
  src += gate;
  src += " ";
  src += delay;
  src +=
      " g(y, a);\n"
      "  always @(y) $display(\"%0t %b\", $time, y);\n"
      "  initial begin\n"
      "    a = 1'b0; #20 a = 1'b1; #20 a = 1'b0;\n"
      "    #20 a = 1'bx; #20 a = 1'b1; #20 a = 1'bz;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

TEST(BufNotSimulation, OneDelayTimesEveryOutputTransition) {
  EXPECT_EQ(BufNotTransitionsShown("buf", "#5"),
            "5 0\n25 1\n45 0\n65 x\n85 1\n105 x\n");
  EXPECT_EQ(BufNotTransitionsShown("not", "#5"),
            "5 1\n25 0\n45 1\n65 x\n85 0\n105 x\n");
}

TEST(BufNotSimulation, AMoveToXTakesTheSmallerOfTwoDelays) {
  EXPECT_EQ(BufNotTransitionsShown("buf", "#(4, 9)"),
            "9 0\n24 1\n49 0\n64 x\n84 1\n104 x\n");
  EXPECT_EQ(BufNotTransitionsShown("buf", "#(9, 4)"),
            "4 0\n29 1\n44 0\n64 x\n89 1\n104 x\n");
  EXPECT_EQ(BufNotTransitionsShown("not", "#(4, 9)"),
            "4 1\n29 0\n44 1\n64 x\n89 0\n104 x\n");
  EXPECT_EQ(BufNotTransitionsShown("not", "#(9, 4)"),
            "9 1\n24 0\n49 1\n64 x\n84 0\n104 x\n");
}

}  // namespace
