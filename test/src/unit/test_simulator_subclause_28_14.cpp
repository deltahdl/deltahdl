#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_network.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/switch_network.h"

using namespace delta;

namespace {

TEST(StrengthReductionResistive, SupplyReducesToPull) {
  EXPECT_EQ(ReduceResistive(Strength::kSupply), Strength::kPull);
}

TEST(StrengthReductionResistive, StrongReducesToPull) {
  EXPECT_EQ(ReduceResistive(Strength::kStrong), Strength::kPull);
}

TEST(StrengthReductionResistive, PullReducesToWeak) {
  EXPECT_EQ(ReduceResistive(Strength::kPull), Strength::kWeak);
}

TEST(StrengthReductionResistive, LargeReducesToMedium) {
  EXPECT_EQ(ReduceResistive(Strength::kLarge), Strength::kMedium);
}

TEST(StrengthReductionResistive, WeakReducesToMedium) {
  EXPECT_EQ(ReduceResistive(Strength::kWeak), Strength::kMedium);
}

TEST(StrengthReductionResistive, MediumReducesToSmall) {
  EXPECT_EQ(ReduceResistive(Strength::kMedium), Strength::kSmall);
}

TEST(StrengthReductionResistive, SmallStaysSmall) {
  EXPECT_EQ(ReduceResistive(Strength::kSmall), Strength::kSmall);
}

TEST(StrengthReductionResistive, HighzStaysHighz) {
  EXPECT_EQ(ReduceResistive(Strength::kHighz), Strength::kHighz);
}

Strength ToStrength(StrengthLevel level) {
  return static_cast<Strength>(static_cast<uint8_t>(level));
}

TEST(StrengthReductionResistive, ModelAndSimulatorReduceSupplyDriveToPull) {
  const StrengthLevel kInput = StrengthLevel::kSupply;
  const StrengthLevel kTableRow = StrengthLevel::kPull;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, ModelAndSimulatorReduceStrongDriveToPull) {
  const StrengthLevel kInput = StrengthLevel::kStrong;
  const StrengthLevel kTableRow = StrengthLevel::kPull;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, ModelAndSimulatorReducePullDriveToWeak) {
  const StrengthLevel kInput = StrengthLevel::kPull;
  const StrengthLevel kTableRow = StrengthLevel::kWeak;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive,
     ModelAndSimulatorReduceLargeCapacitorToMedium) {
  const StrengthLevel kInput = StrengthLevel::kLarge;
  const StrengthLevel kTableRow = StrengthLevel::kMedium;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, ModelAndSimulatorReduceWeakDriveToMedium) {
  const StrengthLevel kInput = StrengthLevel::kWeak;
  const StrengthLevel kTableRow = StrengthLevel::kMedium;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive,
     ModelAndSimulatorReduceMediumCapacitorToSmall) {
  const StrengthLevel kInput = StrengthLevel::kMedium;
  const StrengthLevel kTableRow = StrengthLevel::kSmall;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, ModelAndSimulatorKeepSmallCapacitorSmall) {
  const StrengthLevel kInput = StrengthLevel::kSmall;
  const StrengthLevel kTableRow = StrengthLevel::kSmall;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, ModelAndSimulatorKeepHighImpedanceHighz) {
  const StrengthLevel kInput = StrengthLevel::kHighz;
  const StrengthLevel kTableRow = StrengthLevel::kHighz;
  EXPECT_EQ(ModelReduceResistive(kInput), kTableRow);
  EXPECT_EQ(ReduceResistive(ToStrength(kInput)), ToStrength(kTableRow));
}

TEST(StrengthReductionResistive, RnmosReducesSupplyDriveToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionResistive, RnmosReducesPullDriveToWeak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kWeak);
}

TEST(StrengthReductionResistive, RnmosReducesWeakDriveToMedium) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (weak1, weak0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  rnmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kMedium);
}

TEST(StrengthReductionResistive, RpmosReducesStrongDriveToPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  rpmos r1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionResistive, RcmosReducesStrongDriveToPull) {
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

TEST(StrengthReductionResistive, NonresistiveNmosDoesNotReduceStrongDrive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (strong1, strong0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

namespace {
struct ResistiveBidirResult {
  NetPair nets;
  NetStrength b_strength;
};

ResistiveBidirResult ReduceAcrossResistiveBidir(BidirSwitchKind kind,
                                                Logic4Word control,
                                                Strength source) {
  ResistiveBidirResult r;
  r.nets = MakeStrengthDrivenNetPair(source);

  std::vector<SwitchInst> sw;
  sw.push_back({&r.nets.a, &r.nets.b, kind, control, false, {}});
  ResolveSwitchNetwork(sw, r.nets.arena);
  r.b_strength = r.nets.b.resolved_strength;
  return r;
}
}  // namespace

TEST(StrengthReductionResistive, Rtranif1ReducesStrongDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {1, 0},
                                      Strength::kStrong);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionResistive, RtranReducesPullDriveToWeak) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtran, {0, 0},
                                      Strength::kPull);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kWeak);
}

TEST(StrengthReductionResistive, Rtranif0ReducesSupplyDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif0, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionResistive, NonconductingRtranif1LeavesFarNetStrength) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

TEST(StrengthReductionResistive,
     ATriregsChargeIsReducedCrossingAResistiveSwitch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg d = 1, g = 1;\n"
      "  trireg (large) t;\n"
      "  wire w1, w2;\n"
      "  nmos (t, d, g);\n"
      "  rtran (t, w1);\n"
      "  tran (t, w2);\n"
      "  initial #1 g = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w1 = f.ctx.FindNet("w1");
  auto* w2 = f.ctx.FindNet("w2");
  ASSERT_NE(w1, nullptr);
  ASSERT_NE(w2, nullptr);
  EXPECT_EQ(w1->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w1->resolved->value.words[0].bval & 0x1, 0u);
  EXPECT_EQ(w1->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(w2->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w2->resolved->value.words[0].bval & 0x1, 0u);
  EXPECT_EQ(w2->resolved_strength.s1_hi, Strength::kLarge);
}

TEST(StrengthReductionResistive, ADataInputThatIsNoWholeNetIsReduced) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic d = 1, c = 1, nc = 1, pc = 0;\n"
      "  supply1 [1:0] s;\n"
      "  wire y1, y2, y3, y4, y5;\n"
      "  rnmos (y1, d, c);\n"
      "  rcmos (y2, d, nc, pc);\n"
      "  rnmos (y3, s[0], c);\n"
      "  rnmos (y4, 1'b1, c);\n"
      "  rnmos (y5, m.s[1], c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  for (const char* name : {"y1", "y2", "y3", "y4", "y5"}) {
    auto* y = f.ctx.FindNet(name);
    ASSERT_NE(y, nullptr) << name;
    EXPECT_EQ(y->resolved->value.ToUint64() & 0x1, 1u) << name;
    EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull) << name;
  }
}

TEST(StrengthReductionResistive, ASwitchPassesAnAmbiguousStrengthAsARange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1, b = 1'bx, on = 1;\n"
      "  wire u, y1, y2;\n"
      "  pmos p (u, a, b);\n"
      "  pullup (u);\n"
      "  nmos n (y1, u, on);\n"
      "  rnmos r (y2, u, on);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y1 = f.ctx.FindNet("y1");
  auto* y2 = f.ctx.FindNet("y2");
  ASSERT_NE(y1, nullptr);
  ASSERT_NE(y2, nullptr);
  EXPECT_EQ(y1->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(y1->resolved->value.words[0].bval & 0x1, 0u);
  EXPECT_EQ(y1->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(y1->resolved_strength.s1_lo, Strength::kPull);
  EXPECT_EQ(y2->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(y2->resolved->value.words[0].bval & 0x1, 0u);
  EXPECT_EQ(y2->resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(y2->resolved_strength.s1_lo, Strength::kWeak);
}

}  // namespace
