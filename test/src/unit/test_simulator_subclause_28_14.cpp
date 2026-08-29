

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_switch_network.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// This file covers the rule of §28.14: "The rnmos, rpmos, rcmos, rtran,
// rtranif1, and rtranif0 devices shall reduce the strength of signals that pass
// through them according to Table 28-8."
//
// The ModelAndSimulator... cases claim more than the cases around them: at
// every row of Table 28-8, ModelReduceResistive in
// lib/cpp/test_models/model_strength.h and ReduceResistive in
// src/common/types.h each produce the reduced strength the table gives. Both
// functions are asserted against the table, so a row where the two agree with
// each other and not with Table 28-8 fails here.
//
// Issue #3417 is the defect those cases answer. The model's function was named
// ReduceResistive as well, so every call written in this file passed a Strength
// and reached the simulator's function in src/common/types.h. The shared name
// is what made the model read as covered while nothing ever called it.

// Row-by-row coverage of Table 28-8 against the exact reduction function the
// simulator lowerer applies for resistive devices.
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

// ModelReduceResistive states Table 28-8 independently of the simulator. Its
// StrengthLevel and the simulator's Strength in src/common/types.h carry the
// same eight levels of §28.11's Table 28-7 at the same underlying values, so a
// level converts by its number.
Strength ToStrength(StrengthLevel level) {
  return static_cast<Strength>(static_cast<uint8_t>(level));
}

// One case per row of Table 28-8, which reads: supply drive to pull drive,
// strong drive to pull drive, pull drive to weak drive, large capacitor to
// medium capacitor, weak drive to medium capacitor, medium capacitor to small
// capacitor, small capacitor to small capacitor, high impedance to high
// impedance.
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

// End-to-end observation that §28.14's reduction rule is what the simulator
// applies when a resistive device passes a signal: a known drive strength is
// assigned to the data net, the conducting resistive switch forwards it, and
// the output net settles with the Table 28-8 reduced strength. These exercise
// the production lowerer path (which selects ReduceResistive for resistive
// switches), not the helper in isolation.

// Supply drive -> Pull drive through an rnmos.
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

// Pull drive -> Weak drive through an rnmos.
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

// Weak drive -> Medium capacitor through an rnmos.
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

// The rule applies to rpmos as well: Strong drive -> Pull drive. rpmos
// conducts when its control is low.
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

// And to rcmos: Strong drive -> Pull drive. The rcmos n-half conducts the
// high data value when its ncontrol is high.
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

// Counterpoint confirming the reduction is specific to resistive routing: the
// same strong drive forwarded by a non-resistive nmos is NOT reduced to pull,
// so the pull result above is produced by §28.14's rule rather than by the
// assign or the switch's value semantics.
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

// §28.14 lists the bidirectional resistive switches rtran, rtranif1, and
// rtranif0 alongside the unidirectional ones: a signal crossing a resistive
// bidirectional switch is reduced by Table 28-8 too. These devices are resolved
// by the standalone bidirectional switch-network resolver (they are not lowered
// into the continuous-assignment path), whose behavior depends only on the
// switch flavor and the source terminal's strength, not on how that strength
// was produced -- so they are exercised directly against the production
// resolver. Terminal a is driven to 1 with a chosen strength, terminal b is
// undriven, and the conducting switch propagates a's value and reduced strength
// onto b; b's resolved strength is what §28.14's rule produces on the far net.
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

// Strong drive -> Pull drive across a conducting rtranif1 (control high).
TEST(StrengthReductionResistive, Rtranif1ReducesStrongDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {1, 0},
                                      Strength::kStrong);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Pull drive -> Weak drive across an rtran, which conducts unconditionally.
TEST(StrengthReductionResistive, RtranReducesPullDriveToWeak) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtran, {0, 0},
                                      Strength::kPull);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kWeak);
}

// Supply drive -> Pull drive across a conducting rtranif0 (control low).
TEST(StrengthReductionResistive, Rtranif0ReducesSupplyDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif0, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Negative form: an rtranif1 held off passes nothing across, so the far net is
// left at its default high-impedance strength -- the resistive reduction never
// runs on a nonconducting switch.
TEST(StrengthReductionResistive, NonconductingRtranif1LeavesFarNetStrength) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

}  // namespace
