

#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_switch_network.h"
#include "simulator/net.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  Arena arena;
  Variable* va = nullptr;
  Variable* vb = nullptr;
  NetStrength b_strength;
};

ResistiveBidirResult ReduceAcrossResistiveBidir(BidirSwitchKind kind,
                                                Logic4Word control,
                                                Strength source) {
  ResistiveBidirResult r;
  r.va = r.arena.Create<Variable>();
  r.va->value = MakeLogic4Vec(r.arena, 1);
  r.vb = r.arena.Create<Variable>();
  r.vb->value = MakeLogic4Vec(r.arena, 1);

  Net a = MakeNet1(r.arena, r.va, 1);
  a.resolved_strength.s1_hi = source;
  a.resolved_strength.s1_lo = source;
  Net b = MakeUndrivenNet(r.arena, r.vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, kind, control, false, {}});
  ResolveSwitchNetwork(sw, r.arena);
  r.b_strength = b.resolved_strength;
  return r;
}
}  // namespace

// Strong drive -> Pull drive across a conducting rtranif1 (control high).
TEST(StrengthReductionResistive, Rtranif1ReducesStrongDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {1, 0},
                                      Strength::kStrong);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Pull drive -> Weak drive across an rtran, which conducts unconditionally.
TEST(StrengthReductionResistive, RtranReducesPullDriveToWeak) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtran, {0, 0},
                                      Strength::kPull);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kWeak);
}

// Supply drive -> Pull drive across a conducting rtranif0 (control low).
TEST(StrengthReductionResistive, Rtranif0ReducesSupplyDriveToPull) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif0, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Negative form: an rtranif1 held off passes nothing across, so the far net is
// left at its default high-impedance strength -- the resistive reduction never
// runs on a nonconducting switch.
TEST(StrengthReductionResistive, NonconductingRtranif1LeavesFarNetStrength) {
  auto r = ReduceAcrossResistiveBidir(BidirSwitchKind::kRtranif1, {0, 0},
                                      Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

}  // namespace
