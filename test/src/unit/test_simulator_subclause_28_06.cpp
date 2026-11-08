#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string DriveTristate(const char* gate, const char* data,
                          const char* ctrl) {
  SimFixture f;
  std::string src = std::string("module t;\n  wire y;\n  logic d, c;\n  ") +
                    gate + " g(y, d, c);\n  initial begin d = " + data +
                    "; c = " + ctrl + "; end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return "<elaborate-failed>";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  EXPECT_NE(var, nullptr);
  return var ? var->value.ToString() : "<no-output>";
}

uint64_t SettleTime(const std::string& decl, const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  logic src, ctrl;\n  " + decl +
                    "\n  initial begin " + stim + " end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.scheduler.CurrentTime().ticks;
}

TEST(TristateGateSim, Bufif1ConductsWhenControlHigh) {
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'b1"), "0");
  EXPECT_EQ(DriveTristate("bufif1", "1'b1", "1'b1"), "1");
  EXPECT_EQ(DriveTristate("bufif1", "1'bx", "1'b1"), "x");
}

TEST(TristateGateSim, Bufif1HighImpedanceWhenControlLow) {
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif1", "1'b1", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif1", "1'bx", "1'b0"), "z");
}

TEST(TristateGateSim, Bufif0ConductsWhenControlLow) {
  EXPECT_EQ(DriveTristate("bufif0", "1'b0", "1'b0"), "0");
  EXPECT_EQ(DriveTristate("bufif0", "1'b1", "1'b0"), "1");
  EXPECT_EQ(DriveTristate("bufif0", "1'bx", "1'b0"), "x");
}

TEST(TristateGateSim, Bufif0HighImpedanceWhenControlHigh) {
  EXPECT_EQ(DriveTristate("bufif0", "1'b0", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'b1", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'bx", "1'b1"), "z");
}

TEST(TristateGateSim, Notif1ConductsAndInvertsWhenControlHigh) {
  EXPECT_EQ(DriveTristate("notif1", "1'b0", "1'b1"), "1");
  EXPECT_EQ(DriveTristate("notif1", "1'b1", "1'b1"), "0");
  EXPECT_EQ(DriveTristate("notif1", "1'bx", "1'b1"), "x");
}

TEST(TristateGateSim, Notif1HighImpedanceWhenControlLow) {
  EXPECT_EQ(DriveTristate("notif1", "1'b0", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("notif1", "1'b1", "1'b0"), "z");
}

TEST(TristateGateSim, Notif0ConductsAndInvertsWhenControlLow) {
  EXPECT_EQ(DriveTristate("notif0", "1'b0", "1'b0"), "1");
  EXPECT_EQ(DriveTristate("notif0", "1'b1", "1'b0"), "0");
  EXPECT_EQ(DriveTristate("notif0", "1'bx", "1'b0"), "x");
}

TEST(TristateGateSim, Notif0HighImpedanceWhenControlHigh) {
  EXPECT_EQ(DriveTristate("notif0", "1'b0", "1'b1"), "z");
  EXPECT_EQ(DriveTristate("notif0", "1'b1", "1'b1"), "z");
}

TEST(TristateGateSim, ConductingGateFoldsHighImpedanceDataToX) {
  EXPECT_EQ(DriveTristate("bufif1", "1'bz", "1'b1"), "x");
  EXPECT_EQ(DriveTristate("bufif0", "1'bz", "1'b0"), "x");
  EXPECT_EQ(DriveTristate("notif1", "1'bz", "1'b1"), "x");
  EXPECT_EQ(DriveTristate("notif0", "1'bz", "1'b0"), "x");
}

TEST(TristateGateSim, BlockedGateStillFloatsWithHighImpedanceData) {
  EXPECT_EQ(DriveTristate("bufif1", "1'bz", "1'b0"), "z");
  EXPECT_EQ(DriveTristate("bufif0", "1'bz", "1'b1"), "z");
}

TEST(TristateGateSim, RiseDelayGovernsZeroToOne) {
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, FallDelayGovernsOneToZero) {
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

TEST(TristateGateSim, TurnOffDelayGovernsTransitionToZ) {
  uint64_t t = SettleTime("bufif1 #(5, 10, 15) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 35u);
}

TEST(TristateGateSim, SmallestDelayGovernsTransitionToX) {
  uint64_t t = SettleTime("bufif1 #(40, 30, 20) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #50 src = 1'bx;");
  EXPECT_EQ(t, 70u);
}

TEST(TristateGateSim, TwoDelayFormUsesSmallerForTurnOff) {
  uint64_t t = SettleTime("bufif1 #(5, 10) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, TwoDelayFormUsesSmallerForTransitionToX) {
  uint64_t t = SettleTime("bufif1 #(5, 10) g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #50 src = 1'bx;");
  EXPECT_EQ(t, 55u);
}

TEST(TristateGateSim, SingleDelayAppliesToEveryTransition) {
  uint64_t t = SettleTime("bufif1 #7 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1; "
                          "#20 src = 1'b0;");
  EXPECT_EQ(t, 47u);
}

TEST(TristateGateSim, NoDelaySpecificationPropagatesImmediately) {
  uint64_t t = SettleTime("bufif1 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 20u);
}

TEST(TristateGateSim, SingleDelayAlsoTimesTurnOff) {
  uint64_t t = SettleTime("bufif1 #7 g(y, src, ctrl);",
                          "ctrl = 1'b1; src = 1'b1; #20 ctrl = 1'b0;");
  EXPECT_EQ(t, 27u);
}

TEST(TristateGateSim, RiseDelayFromParameterGovernsTransition) {
  uint64_t t =
      SettleTime("parameter P = 5;\n  bufif1 #(P, 10, 15) g(y, src, ctrl);",
                 "ctrl = 1'b1; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(TristateGateSim, FallDelayFromLocalparamGovernsTransition) {
  uint64_t t =
      SettleTime("localparam Q = 10;\n  bufif1 #(5, Q, 15) g(y, src, ctrl);",
                 "ctrl = 1'b1; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

std::string DriveTristateStrength(const std::string& decl,
                                  const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  " + decl + "\n  initial begin " +
                    stim + " #1 $display(\"%v\", y); end\nendmodule\n";
  return RunCapture(src, f);
}

TEST(TristateGateSim, Bufif1WithUnknownControlDrivesStrongH) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  bufif1 g(y, d, c);",
                                  "d = 1'b1; c = 1'bx;"),
            "StH\n");
}

TEST(TristateGateSim, Bufif0WithUnknownControlDrivesStrongLFromAWeakInput) {
  EXPECT_EQ(DriveTristateStrength(
                "wire d;\n  logic c;\n"
                "  assign (weak0, weak1) d = 1'b0;\n  bufif0 g(y, d, c);",
                "c = 1'bx;"),
            "StL\n");
}

TEST(TristateGateSim, Bufif1WithUnknownControlReadsAsUnknown) {
  EXPECT_EQ(DriveTristate("bufif1", "1'b0", "1'bx"), "x");
}

TEST(TristateGateSim, Notif1WithUnknownControlDrivesTheInvertedSide) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  notif1 g(y, d, c);",
                                  "d = 1'b0; c = 1'bx;"),
            "StH\n");
}

TEST(TristateGateSim, Bufif1WithHighImpedanceControlDrivesStrongH) {
  EXPECT_EQ(DriveTristateStrength("logic d;\n  wire c;\n  bufif1 g(y, d, c);",
                                  "d = 1'b1;"),
            "StH\n");
}

TEST(TristateGateSim, StrongHAgainstAWeakerZeroRendersTheTwoDigitForm) {
  EXPECT_EQ(DriveTristateStrength("logic d, c;\n  bufif1 g(y, d, c);\n"
                                  "  assign (pull0, pull1) y = 1'b0;",
                                  "d = 1'b1; c = 1'bx;"),
            "56X\n");
}

TEST(TristateGateSim, InoutPortDriversResolveWithAPullup) {
  SimFixture f;
  auto out = RunCapture(
      "module drv (inout w, input d, en);\n"
      "  bufif1 g (w, d, en);\n"
      "endmodule\n"
      "module top;\n"
      "  wire bus;\n"
      "  pullup (bus);\n"
      "  logic d1 = 1, e1 = 1, d2 = 0, e2 = 0;\n"
      "  drv a (bus, d1, e1);\n"
      "  drv b (bus, d2, e2);\n"
      "  initial begin\n"
      "    #1 $display(\"bus=%b %v\", bus, bus);\n"
      "    e1 = 0; e2 = 1;\n"
      "    #1 $display(\"bus=%b %v\", bus, bus);\n"
      "    e2 = 0;\n"
      "    #1 $display(\"bus=%b %v\", bus, bus);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "bus=1 St1\n"
            "bus=0 St0\n"
            "bus=1 Pu1\n");
}

TEST(TristateGateSim, InoutPortDriverResolvesWithAGateDeclaredBeforeIt) {
  SimFixture f;
  auto out = RunCapture(
      "module drv (inout w, input d, en);\n"
      "  bufif1 g (w, d, en);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w1, w3;\n"
      "  logic one = 1, zero = 0, e1 = 1, e2 = 0;\n"
      "  drv a1 (w1, one, e1);\n"
      "  drv a2 (w1, zero, e2);\n"
      "  bufif1 c1 (w3, one, e1);\n"
      "  drv c2 (w3, zero, e2);\n"
      "  initial begin\n"
      "    #1 $display(\"w1=%b w3=%b\", w1, w3);\n"
      "    e1 = 0; e2 = 1;\n"
      "    #1 $display(\"w1=%b w3=%b\", w1, w3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "w1=1 w3=1\n"
            "w1=0 w3=0\n");
}

}  // namespace
