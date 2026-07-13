

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

TEST(StrengthReductionNonresistive, SupplyReducesToStrong) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSupply), Strength::kStrong);
}

TEST(StrengthReductionNonresistive, StrongPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kStrong), Strength::kStrong);
}

TEST(StrengthReductionNonresistive, PullPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kPull), Strength::kPull);
}

TEST(StrengthReductionNonresistive, LargePassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kLarge), Strength::kLarge);
}

TEST(StrengthReductionNonresistive, WeakPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kWeak), Strength::kWeak);
}

TEST(StrengthReductionNonresistive, MediumPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kMedium), Strength::kMedium);
}

TEST(StrengthReductionNonresistive, SmallPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSmall), Strength::kSmall);
}

TEST(StrengthReductionNonresistive, HighzPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kHighz), Strength::kHighz);
}

// The cases above pin the reduction table in isolation. The simulations below
// drive a real switch so the rule is observed exactly as production applies it
// during elaboration + lowering: a nonresistive switch (nmos/pmos/cmos) carries
// the data input's strength to its output, and a supply-strength source is the
// single case that is knocked down — to strong.
TEST(StrengthReductionNonresistive, NmosForwardsNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  nmos n1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionNonresistive, NmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
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

TEST(StrengthReductionNonresistive, PmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, CmosReducesSupplySourceToStrong) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (supply1, supply0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b0;\n"
      "  cmos g1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

// The "except" clause is a single case: for pmos and cmos too, any non-supply
// data strength is passed to the output unchanged. These complete the
// passthrough half of §28.13's first sentence for the two devices whose
// supply-reduction is shown above.
TEST(StrengthReductionNonresistive, PmosForwardsNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, c;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign c = 1'b0;\n"
      "  pmos p1(y, d, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionNonresistive, CmosForwardsNonSupplyStrengthUnchanged) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire y, d, nc, pc;\n"
      "  assign (pull1, pull0) d = 1'b1;\n"
      "  assign nc = 1'b1;\n"
      "  assign pc = 1'b0;\n"
      "  cmos g1(y, d, nc, pc);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kPull);
}

// §28.13, second sentence: the tran, tranif0, and tranif1 switches do not
// affect signal strength across their bidirectional terminals, except that a
// supply strength is reduced to a strong strength. Bidirectional switches are
// resolved by the switch-network subsystem (they are not lowered into the
// continuous-assignment path), so these observe the rule through that resolver.
// Terminal a is driven to 1 with a chosen strength; terminal b is undriven, so
// the conducting switch propagates a's value and strength onto b, and b's
// resolved strength is what the rule produces on the far terminal.
namespace {
struct BidirStrengthResult {
  Arena arena;
  Variable* va = nullptr;
  Variable* vb = nullptr;
  NetStrength b_strength;
};

BidirStrengthResult ResolveAcrossBidir(BidirSwitchKind kind, Logic4Word control,
                                       Strength source) {
  BidirStrengthResult r;
  r.va = r.arena.Create<Variable>();
  r.va->value = MakeLogic4Vec(r.arena, 1);
  r.vb = r.arena.Create<Variable>();
  r.vb->value = MakeLogic4Vec(r.arena, 1);

  Net a = MakeNet1(r.arena, r.va, 1);
  a.resolved_strength.s1_hi = source;
  a.resolved_strength.s1_lo = source;
  Net b = MakeUndrivenNet(r.arena, r.vb);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&a, &b, kind, control, false});
  ResolveBidirSwitchNetwork(sw, r.arena);
  r.b_strength = b.resolved_strength;
  return r;
}
}  // namespace

TEST(StrengthReductionNonresistive, TranReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTran, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, TranPassesPullSourceUnchanged) {
  auto r = ResolveAcrossBidir(BidirSwitchKind::kTran, {0, 0}, Strength::kPull);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionNonresistive, Tranif1ReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {1, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, Tranif0PassesStrongSourceUnchanged) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif0, {0, 0}, Strength::kStrong);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

// Complete the device x behavior matrix for the second sentence: tranif0 also
// knocks a supply source down to strong, and tranif1 passes a non-supply (pull)
// source across untouched.
TEST(StrengthReductionNonresistive, Tranif0ReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif0, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, Tranif1PassesPullSourceUnchanged) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {1, 0}, Strength::kPull);
  EXPECT_EQ(ValOf(*r.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Negative form: when the pass-enable control turns the switch off nothing
// crosses the terminals, so no strength is imposed on the far net -- it keeps
// its default high-impedance strength.
TEST(StrengthReductionNonresistive, NonconductingTranif1LeavesFarNetStrength) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

}  // namespace
