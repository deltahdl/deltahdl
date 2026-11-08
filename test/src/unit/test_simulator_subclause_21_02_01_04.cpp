#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

NetStrength MakeNS(Strength s0_hi, Strength s0_lo, Strength s1_hi,
                   Strength s1_lo) {
  NetStrength ns;
  ns.s0_hi = s0_hi;
  ns.s0_lo = s0_lo;
  ns.s1_hi = s1_hi;
  ns.s1_lo = s1_lo;
  return ns;
}

std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

void ExpectPercentVOutput(const std::string& src, const std::string& expected) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(src, f);
  EXPECT_NE(out.find(expected), std::string::npos);
}

void ExpectPercentVReported(const std::string& decl, const std::string& operand,
                            const std::string& shape) {
  SimFixture f;
  const std::string kSrc = "module m;\n  " + decl +
                           "\n  initial $display(\"%v\", " + operand +
                           ");\nendmodule\n";
  CaptureDisplayOutput(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "%v format specification takes a scalar reference, and the argument it "
      "consumed is " +
          shape,
      LineHolding(kSrc, "$display"), "21.2.1.4"));
}

void ExpectPercentVOperandReported(const std::string& decl) {
  ExpectPercentVReported(decl, "w", "a net declared with a range");
}

void ExpectPercentVNotReported(const std::string& src) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(src, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << out;
}

TEST(StrengthFormat, StrongDriveOneIsSt1) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kStrong, Strength::kStrong)),
            "St1");
}

TEST(StrengthFormat, PullDriveZeroIsPu0) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kPull,
                                  Strength::kHighz, Strength::kHighz)),
            "Pu0");
}

TEST(StrengthFormat, UndrivenNetIsHiZ) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kHighz, Strength::kHighz)),
            "HiZ");
}

TEST(StrengthFormat, MediumCapacitorZeroIsMe0) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kMedium, Strength::kMedium,
                                  Strength::kHighz, Strength::kHighz)),
            "Me0");
}

TEST(StrengthFormat, StrongUnknownSameLevelIsStX) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kHighz,
                                  Strength::kStrong, Strength::kHighz)),
            "StX");
}

TEST(StrengthFormat, PullOneOrHighZIsPuH) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kPull, Strength::kHighz)),
            "PuH");
}

TEST(StrengthFormat, UnknownDifferentLevelsIs65X) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kStrong,
                                  Strength::kPull, Strength::kPull)),
            "65X");
}

TEST(StrengthFormat, UnknownDifferentLevelsKeepsZeroThenOneOrder) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kPull,
                                  Strength::kStrong, Strength::kStrong)),
            "56X");
}

TEST(StrengthFormat, UnknownRenderingIgnoresTheLowerBounds) {
  const std::string kCollapsed =
      FormatStrength(MakeNS(Strength::kStrong, Strength::kStrong,
                            Strength::kStrong, Strength::kStrong));
  const std::string kOneSideRanged =
      FormatStrength(MakeNS(Strength::kStrong, Strength::kStrong,
                            Strength::kStrong, Strength::kPull));
  EXPECT_EQ(kOneSideRanged, kCollapsed);
  EXPECT_EQ(kOneSideRanged, "StX");
}

TEST(StrengthFormat, UnknownWithBothSidesRangedPrintsTheTwoHighestLevels) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kWeak,
                                  Strength::kStrong, Strength::kPull)),
            "56X");
}

TEST(StrengthFormat, UnknownFromCombinedAmbiguousStrengthsIs35X) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kWeak, Strength::kHighz,
                                  Strength::kPull, Strength::kHighz)),
            "35X");
}

TEST(StrengthFormat, ZeroAcrossRangeIs520) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kPull, Strength::kMedium,
                                  Strength::kHighz, Strength::kHighz)),
            "520");
}

TEST(StrengthFormat, OneAcrossRangeIsDigitsThenValue) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kStrong, Strength::kPull)),
            "651");
}

TEST(StrengthFormat, ZeroOrHighZIsMnemonicL) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kStrong, Strength::kHighz,
                                  Strength::kHighz, Strength::kHighz)),
            "StL");
}

TEST(StrengthFormat, AllStrengthLevelMnemonicsAreReachable) {
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kSupply, Strength::kSupply)),
            "Su1");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kLarge, Strength::kLarge,
                                  Strength::kHighz, Strength::kHighz)),
            "La0");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kHighz, Strength::kHighz,
                                  Strength::kWeak, Strength::kWeak)),
            "We1");
  EXPECT_EQ(FormatStrength(MakeNS(Strength::kSmall, Strength::kSmall,
                                  Strength::kHighz, Strength::kHighz)),
            "Sm0");
}

TEST(StrengthFormat, PercentVConsumesOneArgumentEach) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 1, 1),
                              MakeLogic4VecVal(arena, 1, 0)};
  std::vector<std::string> v_fmts{"St1", "Pu0"};
  auto out = FormatDisplay("a=%v b=%v", vals, {.v_fmts = &v_fmts, .loc = {}});
  EXPECT_EQ(out, "a=St1 b=Pu0");
}

TEST(StrengthFormat, PercentVUppercaseMatchesLowercase) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 1, 0)};
  std::vector<std::string> v_fmts{"StX"};
  EXPECT_EQ(FormatDisplay("%V", vals, {.v_fmts = &v_fmts, .loc = {}}),
            FormatDisplay("%v", vals, {.v_fmts = &v_fmts, .loc = {}}));
}

TEST(StrengthFormat, ResolvedNetStrengthRendersStrongDriveOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(FormatStrength(net->resolved_strength), "St1");
}

TEST(StrengthFormat, ResolvedNetStrengthRendersStrongDriveZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(FormatStrength(net->resolved_strength), "St0");
}

TEST(StrengthFormat, DisplayPercentVPrintsNetStrength) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("St1"), std::string::npos);
}

TEST(StrengthFormat, PercentVConsumesItsArgumentWithoutAStrengthString) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 5),
                              MakeLogic4VecVal(arena, 8, 9)};
  std::vector<std::string> v_fmts{""};
  auto out = FormatDisplay("%v=%d", vals, {.v_fmts = &v_fmts, .loc = {}});
  EXPECT_EQ(out.find('5'), std::string::npos);
  EXPECT_NE(out.find('9'), std::string::npos);
}

TEST(StrengthFormat, PercentVWithoutArgumentEmitsNothing) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%v", vals);
  EXPECT_TRUE(out.empty());
}

TEST(StrengthFormat, UndrivenWireDisplaysAsHiZ) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("HiZ"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnTriregShowsChargeStorageMnemonic) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  logic en;\n"
      "  trireg (large) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "    $display(\"%v\", cap);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("La1"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnPullDrivenNetShowsPu1) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Pu1"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnWeakDrivenNetShowsWe0) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("We0"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnSupplyDrivenNetShowsSu1) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Su1"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnWeakConflictShowsWeX) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      "WeX");
}

TEST(StrengthFormat, DisplayPercentVOnStrongConflictShowsStX) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  assign w = 1'b0;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      "StX");
}

TEST(StrengthFormat, DisplayPercentVOnStrongDrivenUnknownShowsStX) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'bx;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      "StX");
}

TEST(StrengthFormat, DisplayPercentVOnPullDrivenUnknownShowsPuX) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'bx;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n",
      "PuX");
}

TEST(StrengthFormat, DisplayPercentVOnSmallTriregShowsSm0) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  logic en;\n"
      "  trireg (small) cap;\n"
      "  assign cap = en ? 1'b0 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "    $display(\"%v\", cap);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Sm0"), std::string::npos);
}

TEST(StrengthFormat, DisplayPercentVOnMediumTriregShowsMe1) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  logic en;\n"
      "  trireg (medium) cap;\n"
      "  assign cap = en ? 1'b1 : 1'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "    $display(\"%v\", cap);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("Me1"), std::string::npos);
}

TEST(StrengthFormat, NonNetOperandToPercentVRendersEmpty) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  reg r;\n"
      "  initial begin\n"
      "    r = 1'b1;\n"
      "    $display(\"[%v]\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("[]"), std::string::npos);
}

TEST(StrengthFormat, VectorNetOperandToPercentVIsReported) {
  ExpectPercentVOperandReported("wire [3:0] w;");
}

TEST(StrengthFormat, SingleBitVectorNetOperandToPercentVIsReported) {
  ExpectPercentVOperandReported("wire [0:0] w;");
}

TEST(StrengthFormat, ScalarNetOperandToPercentVIsNotReported) {
  ExpectPercentVNotReported(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "  initial #1 $display(\"%v\", w);\n"
      "endmodule\n");
}

TEST(StrengthFormat, VectorNetUnderAnIntegerSpecifierIsNotReported) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module m;\n"
      "  wire [3:0] w;\n"
      "  assign w = 4'ha;\n"
      "  initial #1 $display(\"[%h]\", w);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << out;
}

TEST(StrengthFormat, BitSelectOfVectorNetRendersThatBitsStrength) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire [3:0] bus;\n"
      "  assign bus = 4'b0001;\n"
      "  initial #1 $display(\"[%v]\", bus[0]);\n"
      "endmodule\n",
      "[St1]");
}

TEST(StrengthFormat, BitSelectReadsTheStrengthOfTheBitItNames) {
  ExpectPercentVOutput(
      "module m;\n"
      "  tri0 [1:0] bus;\n"
      "  assign bus = 2'bz1;\n"
      "  initial #1 $display(\"[%v][%v]\", bus[0], bus[1]);\n"
      "endmodule\n",
      "[St1][Pu0]");
}

TEST(StrengthFormat, BitSelectResolvesItsIndexAgainstTheDeclaredRange) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire [1:2] bus;\n"
      "  assign bus = 2'b01;\n"
      "  initial #1 $display(\"[%v][%v]\", bus[1], bus[2]);\n"
      "endmodule\n",
      "[St0][St1]");
}

TEST(StrengthFormat, OutOfRangeBitSelectOfNetRendersNothing) {
  ExpectPercentVOutput(
      "module m;\n"
      "  wire [3:0] bus;\n"
      "  assign bus = 4'b0001;\n"
      "  initial #1 $display(\"[%v]\", bus[7]);\n"
      "endmodule\n",
      "[]");
}

TEST(StrengthFormat, OutOfRangeBitSelectOfNetIsNotReported) {
  ExpectPercentVNotReported(
      "module m;\n"
      "  wire [3:0] bus;\n"
      "  assign bus = 4'b0001;\n"
      "  initial #1 $display(\"[%v]\", bus[7]);\n"
      "endmodule\n");
}

TEST(StrengthFormat, BitSelectOfVectorNetOperandIsNotReported) {
  ExpectPercentVNotReported(
      "module m;\n"
      "  wire [3:0] bus;\n"
      "  assign bus = 4'b0001;\n"
      "  initial #1 $display(\"%v\", bus[0]);\n"
      "endmodule\n");
}

TEST(StrengthFormat, PartSelectOfNetOperandToPercentVIsReported) {
  ExpectPercentVReported("wire [3:0] w;", "w[1:0]",
                         "a select naming more than one bit of a net");
}

TEST(StrengthFormat, PackedElementSelectOfNetOperandToPercentVIsReported) {
  ExpectPercentVReported("wire [1:0][7:0] w;", "w[0]",
                         "a select naming more than one bit of a net");
}

TEST(StrengthFormat, NetOfASubmoduleNamedHierarchically) {
  SimFixture f;
  auto out = RunCapture(
      "module sub (input a, b);\n"
      "  wire y, z;\n"
      "  and g1 (y, a, b);\n"
      "  nor (weak1, weak0) g2 (z, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a = 1, b = 1;\n"
      "  sub s (a, b);\n"
      "  initial #1 $display(\"y=%b %v z=%b %v\", s.y, s.y, s.z, s.z);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=1 St1 z=0 We0\n");
}

TEST(StrengthFormat, NetOfAnInterfaceInstanceDrivenThroughItsPort) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  wire y, z;\n"
      "endinterface\n"
      "module drv (bus b, input a, c);\n"
      "  and g1 (b.y, a, c);\n"
      "  nor (weak1, weak0) g2 (b.z, a, c);\n"
      "endmodule\n"
      "module top;\n"
      "  bus b();\n"
      "  logic a = 1, c = 1;\n"
      "  drv d (b, a, c);\n"
      "  initial #1 $display(\"y=%b %v z=%b %v\", b.y, b.y, b.z, b.z);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=1 St1 z=0 We0\n");
}

TEST(StrengthFormat, InterfaceNetNamedThroughThePortAndTheInstance) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  wire y;\n"
      "endinterface\n"
      "module drv (bus p, input a);\n"
      "  buf (pull1, pull0) g1 (p.y, a);\n"
      "  initial #2 $display(\"drv %v\", p.y);\n"
      "endmodule\n"
      "module top;\n"
      "  bus i();\n"
      "  logic a = 1;\n"
      "  drv d (i, a);\n"
      "  initial #1 $display(\"top %v\", i.y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "top Pu1\ndrv Pu1\n");
}

}  // namespace
