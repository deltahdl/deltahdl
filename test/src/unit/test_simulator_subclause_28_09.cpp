#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_settle.h"
#include "model_switch_eval.h"
#include "model_val4.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(CmosSwitches, CmosIsNmosPlusPmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kCmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, RcmosIsRnmosPlusRpmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kRcmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, CmosMaxThreeDelays) {
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kCmos), 3u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRcmos), 3u);
}

TEST(CmosSwitches, CmosAcceptsDelaySpec) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kCmos));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRcmos));
}

TEST(CmosSwitches, CmosIsNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kCmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRcmos));
}

TEST(CmosSwitches, CmosBlocksHighZData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, CmosPassesZeroData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
}

TEST(CmosSwitches, CmosPassesDataLowWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, CmosPassesDataHighWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosPassesDataLowWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, CmosPassesDataHighWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosBlocksOutputWhenBothHalvesOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosPassesDataWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, RcmosBlocksOutputWhenBothHalvesOff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosPassesDataLowWhenNcontrolHigh) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b0;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 0u));
}

TEST(CmosSwitches, RcmosPassesDataHighWhenPcontrolLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'b1;\n"
      "  assign nc = 1'b0;\n"
      "  assign pc = 1'b0;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToKnown(f, "y", 1u));
}

TEST(CmosSwitches, CmosPassesHighZDataAsHighZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign d = 1'bz;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(SettledToHighZ(f, "y"));
}

TEST(CmosSwitches, RcmosReducesForwardedStrengthPerResistiveRule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  rcmos r1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(CmosSwitches, CmosLeavesForwardedNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b1;\n"
      "  cmos c1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

uint64_t CmosSettleTime(const std::string& decl, const std::string& stim) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  logic src, nc, pc;\n  " + decl +
                    "\n  initial begin " + stim + " end\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.scheduler.CurrentTime().ticks;
}

TEST(CmosSwitches, CmosRiseDelayGovernsZeroToOne) {
  uint64_t t =
      CmosSettleTime("cmos #(5, 10, 15) g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 25u);
}

TEST(CmosSwitches, CmosFallDelayGovernsOneToZero) {
  uint64_t t =
      CmosSettleTime("cmos #(5, 10, 15) g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;");
  EXPECT_EQ(t, 30u);
}

TEST(CmosSwitches, CmosTwoDelaysUseRiseThenFall) {
  EXPECT_EQ(CmosSettleTime("cmos #(5, 10) g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            25u);
  EXPECT_EQ(CmosSettleTime("cmos #(5, 10) g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;"),
            30u);
}

TEST(CmosSwitches, CmosSingleDelayAppliesToEveryTransition) {
  EXPECT_EQ(CmosSettleTime("cmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            27u);
  EXPECT_EQ(CmosSettleTime("cmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b1; #20 src = 1'b0;"),
            27u);
}

TEST(CmosSwitches, CmosNoDelaySpecPropagatesWithoutDelay) {
  uint64_t t =
      CmosSettleTime("cmos g(y, src, nc, pc);",
                     "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;");
  EXPECT_EQ(t, 20u);
}

TEST(CmosSwitches, RcmosSingleDelayAppliesToEveryTransition) {
  EXPECT_EQ(CmosSettleTime("rcmos #7 g(y, src, nc, pc);",
                           "nc = 1'b1; pc = 1'b0; src = 1'b0; #20 src = 1'b1;"),
            27u);
}

TEST(CmosSwitchSim, AnUnknownControlDrivesTheLOrHOfThePairedSwitches) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic d0 = 0, d1 = 1, dz = 1'bz, nx = 1'bx, poff = 1, px = 1'bx;\n"
      "  wire y1, y2, y3;\n"
      "  cmos (y1, d0, nx, poff);\n"
      "  cmos (y2, d1, nx, px);\n"
      "  cmos (y3, dz, nx, px);\n"
      "  initial #1 $display(\"%v %v %b\", y1, y2, y3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "StL StH z\n");
}

std::string StrengthPassedShown(const std::string& sources,
                                const std::string& data) {
  std::string src = "module t;\n";
  src += sources;
  src +=
      "  logic on1 = 1, on0 = 0;\n"
      "  wire [3:0] y;\n";
  const char* const kSwitches[] = {"nmos g0(y[0], ", "pmos g1(y[1], ",
                                   "cmos g2(y[2], ", "cmos g3(y[3], "};
  const char* const kControls[] = {", on1);\n", ", on0);\n", ", on1, on1);\n",
                                   ", on0, on0);\n"};
  for (std::size_t i = 0; i < std::size(kSwitches); ++i) {
    src += "  ";
    src += kSwitches[i];
    src += data;
    src += kControls[i];
  }
  src +=
      "  initial #2 $display(\"%v %v %v %v\", y[0], y[1], y[2], y[3]);\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

struct PassedStrength {
  const char* sources;
  const char* data;
  const char* shown;
};

TEST(CmosSwitchSim, NonresistiveSwitchesPassEachStrengthButSupply) {
  const PassedStrength kCases[] = {
      {"  supply0 d;\n", "d", "St0 St0 St0 St0\n"},
      {"  supply1 d;\n", "d", "St1 St1 St1 St1\n"},
      {"  supply1 [1:0] s;\n", "s[1]", "St1 St1 St1 St1\n"},
      {"  supply0 [1:0] s;\n", "s[0]", "St0 St0 St0 St0\n"},
      {"  wire d;\n  assign (weak0, weak1) d = 1'b0;\n", "d",
       "We0 We0 We0 We0\n"},
      {"  wire d;\n  assign (pull0, pull1) d = 1'b1;\n", "d",
       "Pu1 Pu1 Pu1 Pu1\n"},
      {"  logic d = 1'b1;\n", "d", "St1 St1 St1 St1\n"},
      {"", "1'b0", "St0 St0 St0 St0\n"},
      {"  trireg (large) d;\n  logic v = 1'b1;\n  assign d = v;\n"
       "  initial #1 v = 1'bz;\n",
       "d", "La1 La1 La1 La1\n"},
      {"  trireg (medium) d;\n  logic v = 1'b0;\n  assign d = v;\n"
       "  initial #1 v = 1'bz;\n",
       "d", "Me0 Me0 Me0 Me0\n"},
      {"  trireg (small) d;\n  logic v = 1'b1;\n  assign d = v;\n"
       "  initial #1 v = 1'bz;\n",
       "d", "Sm1 Sm1 Sm1 Sm1\n"}};
  for (const auto& c : kCases) {
    EXPECT_EQ(StrengthPassedShown(c.sources, c.data), c.shown)
        << c.sources << c.data;
  }
}

TEST(CmosSwitchSim, DISABLED_AHierarchicalDataInputPassesItsStrength) {
  EXPECT_EQ(StrengthPassedShown(
                "  wire w;\n  assign (weak0, weak1) w = 1'b1;\n", "t.w"),
            "We1 We1 We1 We1\n");
}

TEST(CmosSwitchSim, RcmosFourthTerminalIsThePChannelControl) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic d = 0, nc = 0, pc = 0;\n"
      "  wire y;\n"
      "  rcmos r(y, d, nc, pc);\n"
      "  initial begin\n"
      "    #1 $write(\"%v \", y);\n"
      "    pc = 1;\n"
      "    #1 $write(\"%v \", y);\n"
      "    nc = 1;\n"
      "    #1 $display(\"%v\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Pu0 HiZ Pu0\n");
}

TEST(CmosSwitchSim, AnUnknownControlOfEitherKindDrivesLOrH) {
  for (const std::string& sw : {"cmos", "rcmos"}) {
    for (const std::string& unknown : {"1'bx", "1'bz"}) {
      std::string src = "module m;\n  logic d0 = 0, d1 = 1, dz = 1'bz, u = ";
      src += unknown;
      src +=
          ", poff = 1;\n"
          "  wire y1, y2, y3;\n  ";
      src += sw + " (y1, d0, u, poff);\n  ";
      src += sw + " (y2, d1, u, u);\n  ";
      src += sw + " (y3, dz, u, u);\n";
      src +=
          "  initial #1 $display(\"%v %v %b\", y1, y2, y3);\n"
          "endmodule\n";
      SimFixture f;
      EXPECT_EQ(RunCapture(src, f),
                sw == "cmos" ? "StL StH z\n" : "PuL PuH z\n")
          << sw << " " << unknown;
    }
  }
}

TEST(CmosSwitchSim, BothKindsRunInLoopAndConditionalGenerateBlocks) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  logic d = 1, nc = 1, pc = 1;\n"
      "  wire [3:0] y;\n"
      "  for (genvar k = 0; k < 2; k++) begin : g\n"
      "    cmos c(y[k], d, nc, pc);\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    rcmos r(y[2], d, nc, pc);\n"
      "  end\n"
      "  case (1)\n"
      "    1: rcmos q(y[3], d, nc, pc);\n"
      "  endcase\n"
      "  initial begin\n"
      "    #1 $write(\"%v %v %v %v \", y[0], y[1], y[2], y[3]);\n"
      "    nc = 0;\n"
      "    #1 $display(\"%b\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "St1 St1 Pu1 Pu1 zzzz\n");
}

std::string CmosTransitionsShown(const std::string& sw,
                                 const std::string& delay, bool start_high) {
  const char* first = start_high ? "1'b1" : "1'b0";
  const char* second = start_high ? "1'b0" : "1'b1";
  std::string src = "module t;\n  logic d, nc, pc = 1'b1;\n  wire y;\n  ";
  src += sw;
  src += " ";
  src += delay;
  src +=
      " g(y, d, nc, pc);\n"
      "  always @(y)\n"
      "    if ($time >= 20) $display(\"%0t %v\", $time, y);\n"
      "  initial begin\n    d = ";
  src += first;
  src += "; nc = 1'b1;\n    #20 d = ";
  src += second;
  src +=
      ";\n"
      "    #20 nc = 1'b0;\n"
      "    #20 nc = 1'b1;\n"
      "    #20 d = 1'bx;\n"
      "    #20 d = ";
  src += first;
  src +=
      ";\n"
      "    #20 nc = 1'bx;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

std::string WithStrength(const std::string& pattern, const std::string& sw) {
  const std::string kLevel = sw == "rcmos" ? "Pu" : "St";
  std::string out;
  for (char ch : pattern) {
    if (ch == '%') {
      out += kLevel;
    } else {
      out += ch;
    }
  }
  return out;
}

struct CmosTiming {
  const char* delay;
  const char* low_first;
  const char* high_first;
};

TEST(CmosSwitchSim, DelaysTimeEachTransitionOfBothKinds) {
  const CmosTiming kCases[] = {
      {"#(7, 3, 9)", "27 %1\n49 HiZ\n67 %1\n83 %X\n103 %0\n123 %L\n",
       "23 %0\n49 HiZ\n63 %0\n83 %X\n107 %1\n123 %H\n"},
      {"#(9, 5, 2)", "29 %1\n42 HiZ\n69 %1\n82 %X\n105 %0\n122 %L\n",
       "25 %0\n42 HiZ\n65 %0\n82 %X\n109 %1\n122 %H\n"},
      {"#(7, 3)", "27 %1\n43 HiZ\n67 %1\n83 %X\n103 %0\n123 %L\n",
       "23 %0\n43 HiZ\n63 %0\n83 %X\n107 %1\n123 %H\n"},
      {"#(3, 7)", "23 %1\n43 HiZ\n63 %1\n83 %X\n107 %0\n123 %L\n",
       "27 %0\n43 HiZ\n67 %0\n83 %X\n103 %1\n123 %H\n"},
      {"#6", "26 %1\n46 HiZ\n66 %1\n86 %X\n106 %0\n126 %L\n",
       "26 %0\n46 HiZ\n66 %0\n86 %X\n106 %1\n126 %H\n"},
      {"", "20 %1\n40 HiZ\n60 %1\n80 %X\n100 %0\n120 %L\n",
       "20 %0\n40 HiZ\n60 %0\n80 %X\n100 %1\n120 %H\n"}};
  for (const std::string& sw : {"cmos", "rcmos"}) {
    for (const auto& timing : kCases) {
      EXPECT_EQ(CmosTransitionsShown(sw, timing.delay, false),
                WithStrength(timing.low_first, sw))
          << sw << " " << timing.delay;
      EXPECT_EQ(CmosTransitionsShown(sw, timing.delay, true),
                WithStrength(timing.high_first, sw))
          << sw << " " << timing.delay;
    }
  }
}

}  // namespace
