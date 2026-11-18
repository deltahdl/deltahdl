#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

void RunAndCheckResolvedWord(const std::string& initial_line,
                             const std::string& gate_line, uint32_t expect_aval,
                             uint32_t expect_bval) {
  SimFixture f;
  auto* design = ElaborateSrc(std::string("module top;\n"
                                          "  logic a, b;\n"
                                          "  wire y;\n") +
                                  initial_line + gate_line + "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, expect_aval);
  EXPECT_EQ(w.bval & 1u, expect_bval);
}

TEST(HighzStrengthOutput, Highz1ProducesZWhenGateComputesOne) {
  RunAndCheckResolvedWord("  initial begin a = 1'b1; b = 1'b1; end\n",
                          "  and (strong0, highz1) g1(y, a, b);\n", 0u, 1u);
}

TEST(HighzStrengthOutput, Highz0ProducesZWhenGateComputesZero) {
  RunAndCheckResolvedWord("  initial begin a = 1'b0; b = 1'b1; end\n",
                          "  and (highz0, strong1) g1(y, a, b);\n", 0u, 1u);
}

TEST(HighzStrengthOutput, Highz1DoesNotAffectZeroOutput) {
  RunAndCheckResolvedWord("  initial begin a = 1'b0; b = 1'b1; end\n",
                          "  and (strong0, highz1) g1(y, a, b);\n", 0u, 0u);
}

TEST(HighzStrengthOutput, Highz0DoesNotAffectOneOutput) {
  RunAndCheckResolvedWord("  initial begin a = 1'b1; b = 1'b1; end\n",
                          "  and (highz0, strong1) g1(y, a, b);\n", 1u, 0u);
}

TEST(Strength01Semantics, Strength0AndStrength1ReachNetDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  and (pull0, supply1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_FALSE(net->driver_strengths.empty());
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kPull);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kSupply);
}

TEST(Strength01Semantics, WeakAndStrongStrengthsReachNetDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire y;\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "  and (weak0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_FALSE(net->driver_strengths.empty());
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kWeak);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kStrong);
}

std::string StrengthsShown(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string GateDrivingOneThenZero(const std::string& gate_line) {
  return StrengthsShown(
      "module top;\n"
      "  logic a;\n"
      "  wire y;\n" +
      gate_line +
      "  initial begin\n"
      "    a = 1'b1; #1 $display(\"%v\", y);\n"
      "    a = 1'b0; #1 $display(\"%v\", y);\n"
      "  end\n"
      "endmodule\n");
}

TEST(DefaultGateStrength, AnNInputGateDrivingZeroShowsStrong0) {
  EXPECT_EQ(StrengthsShown("module top;\n"
                           "  logic a, b;\n"
                           "  wire y, z;\n"
                           "  and g(y, a, b);\n"
                           "  nor h(z, b, b);\n"
                           "  initial begin\n"
                           "    a = 1'b0; b = 1'b1;\n"
                           "    #1 $display(\"%v %v\", y, z);\n"
                           "  end\n"
                           "endmodule\n"),
            "St0 St0\n");
}

TEST(Strength01Semantics, EachOutputValueDrivesAtItsOwnStrength) {
  EXPECT_EQ(GateDrivingOneThenZero("  and (weak0, pull1) g(y, a, a);\n"),
            "Pu1\nWe0\n");
  EXPECT_EQ(GateDrivingOneThenZero("  and (supply0, weak1) g(y, a, a);\n"),
            "We1\nSu0\n");
  EXPECT_EQ(GateDrivingOneThenZero("  or (strong0, pull1) g(y, a, a);\n"),
            "Pu1\nSt0\n");
}

TEST(Strength01Semantics, Strength1WrittenFirstOnAGate) {
  EXPECT_EQ(GateDrivingOneThenZero("  buf (weak1, pull0) g(y, a);\n"),
            "We1\nPu0\n");
}

TEST(Strength01Semantics, AUdpInstanceDrivesAtItsStrengthPair) {
  EXPECT_EQ(StrengthsShown("primitive u(output y, input a);\n"
                           "  table 0 : 0; 1 : 1; endtable\n"
                           "endprimitive\n"
                           "module top;\n"
                           "  logic a;\n"
                           "  wire y;\n"
                           "  u (weak1, pull0) i(y, a);\n"
                           "  initial begin\n"
                           "    a = 1'b1; #1 $display(\"%v\", y);\n"
                           "    a = 1'b0; #1 $display(\"%v\", y);\n"
                           "  end\n"
                           "endmodule\n"),
            "We1\nPu0\n");
}

TEST(Strength01Semantics, AContinuousAssignmentInAnInterfaceDrivesAtIt) {
  EXPECT_EQ(StrengthsShown("interface i;\n"
                           "  wire y;\n"
                           "  assign (weak1, pull0) y = 1'b1;\n"
                           "endinterface\n"
                           "module top;\n"
                           "  i u();\n"
                           "  initial #1 $display(\"%v\", u.y);\n"
                           "endmodule\n"),
            "We1\n");
}

TEST(Strength01Semantics, AContinuousAssignmentInAProgramDrivesAtIt) {
  EXPECT_EQ(StrengthsShown("program p;\n"
                           "  wire y;\n"
                           "  assign (pull1, weak0) y = 1'b0;\n"
                           "  initial #1 $display(\"%v\", y);\n"
                           "endprogram\n"
                           "module top;\n"
                           "  p u();\n"
                           "endmodule\n"),
            "We0\n");
}

std::string EnableGateShown(const std::string& gate_line) {
  return StrengthsShown(
      "module top;\n"
      "  logic a, c;\n"
      "  wire y;\n" +
      gate_line +
      "  initial begin\n"
      "    c = 1'b1; a = 1'b1; #1 $display(\"%v\", y);\n"
      "    a = 1'b0; #1 $display(\"%v\", y);\n"
      "    c = 1'b0; #1 $display(\"%v\", y);\n"
      "  end\n"
      "endmodule\n");
}

TEST(HighzStrengthOutput, AnEnableGateOutputsZOnItsHighzSide) {
  EXPECT_EQ(EnableGateShown("  bufif1 (highz1, strong0) g(y, a, c);\n"),
            "HiZ\nSt0\nHiZ\n");
  EXPECT_EQ(EnableGateShown("  bufif1 (strong1, highz0) g(y, a, c);\n"),
            "St1\nHiZ\nHiZ\n");
  EXPECT_EQ(EnableGateShown("  notif1 (highz1, strong0) g(y, a, c);\n"),
            "St0\nHiZ\nHiZ\n");
}

TEST(HighzStrengthOutput, AnActiveLowEnableGateOutputsZOnItsHighzSide) {
  EXPECT_EQ(StrengthsShown("module top;\n"
                           "  logic a, n;\n"
                           "  wire y, z;\n"
                           "  notif0 (highz1, strong0) g(y, a, n);\n"
                           "  bufif0 (strong1, highz0) h(z, a, n);\n"
                           "  initial begin\n"
                           "    n = 1'b0; a = 1'b0;\n"
                           "    #1 $display(\"%v %v\", y, z);\n"
                           "    a = 1'b1; #1 $display(\"%v %v\", y, z);\n"
                           "    n = 1'b1; #1 $display(\"%v %v\", y, z);\n"
                           "  end\n"
                           "endmodule\n"),
            "HiZ HiZ\nSt0 St1\nHiZ HiZ\n");
}

}  // namespace
