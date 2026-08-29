

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

// This file covers the two rules of §28.13. "The nmos, pmos, and cmos switches
// shall pass the strength from the data input to the output, except that a
// supply strength shall be reduced to a strong strength." "The tran, tranif0,
// and tranif1 switches shall not affect signal strength across the
// bidirectional terminals, except that a supply strength shall be reduced to a
// strong strength."
//
// The ModelAndSimulator... cases claim more than the cases around them: at each
// of the eight strength levels, ModelReduceNonresistive in
// lib/cpp/test_models/model_strength.h and ReduceNonresistive in
// src/common/types.h each produce the level §28.13 names. Both functions are
// asserted against the clause, so a level where the two agree with each other
// and not with §28.13 fails here.
//
// Issue #3417 is the defect those cases answer. The model's function was named
// ReduceNonresistive as well, so every call written in this file passed a
// Strength and reached the simulator's function in src/common/types.h. The
// shared name is what made the model read as covered while nothing ever called
// it.

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

// ModelReduceNonresistive states §28.13's rule independently of the simulator.
// Its StrengthLevel and the simulator's Strength in src/common/types.h carry
// the same eight levels of §28.11's Table 28-7 at the same underlying values,
// so a level converts by its number.
Strength ToStrength(StrengthLevel level) {
  return static_cast<Strength>(static_cast<uint8_t>(level));
}

// One case per level of the strength scale. §28.13 reduces supply to strong and
// passes every other level from the data input to the output unchanged.
TEST(StrengthReductionNonresistive, ModelAndSimulatorReduceSupplyToStrong) {
  const StrengthLevel kInput = StrengthLevel::kSupply;
  const StrengthLevel kClause = StrengthLevel::kStrong;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassStrongUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kStrong;
  const StrengthLevel kClause = StrengthLevel::kStrong;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassPullUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kPull;
  const StrengthLevel kClause = StrengthLevel::kPull;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassLargeUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kLarge;
  const StrengthLevel kClause = StrengthLevel::kLarge;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassWeakUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kWeak;
  const StrengthLevel kClause = StrengthLevel::kWeak;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassMediumUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kMedium;
  const StrengthLevel kClause = StrengthLevel::kMedium;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassSmallUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kSmall;
  const StrengthLevel kClause = StrengthLevel::kSmall;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
}

TEST(StrengthReductionNonresistive, ModelAndSimulatorPassHighzUnchanged) {
  const StrengthLevel kInput = StrengthLevel::kHighz;
  const StrengthLevel kClause = StrengthLevel::kHighz;
  EXPECT_EQ(ModelReduceNonresistive(kInput), kClause);
  EXPECT_EQ(ReduceNonresistive(ToStrength(kInput)), ToStrength(kClause));
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
  NetPair nets;
  NetStrength b_strength;
};

BidirStrengthResult ResolveAcrossBidir(BidirSwitchKind kind, Logic4Word control,
                                       Strength source) {
  BidirStrengthResult r;
  r.nets = MakeStrengthDrivenNetPair(source);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&r.nets.a, &r.nets.b, kind, control, false});
  ResolveBidirSwitchNetwork(sw, r.nets.arena);
  r.b_strength = r.nets.b.resolved_strength;
  return r;
}
}  // namespace

TEST(StrengthReductionNonresistive, TranReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTran, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, TranPassesPullSourceUnchanged) {
  auto r = ResolveAcrossBidir(BidirSwitchKind::kTran, {0, 0}, Strength::kPull);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

TEST(StrengthReductionNonresistive, Tranif1ReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {1, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, Tranif0PassesStrongSourceUnchanged) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif0, {0, 0}, Strength::kStrong);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

// Complete the device x behavior matrix for the second sentence: tranif0 also
// knocks a supply source down to strong, and tranif1 passes a non-supply (pull)
// source across untouched.
TEST(StrengthReductionNonresistive, Tranif0ReducesSupplySourceToStrong) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif0, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kStrong);
}

TEST(StrengthReductionNonresistive, Tranif1PassesPullSourceUnchanged) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {1, 0}, Strength::kPull);
  EXPECT_EQ(ValOf(*r.nets.vb), kVal1);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kPull);
}

// Negative form: when the pass-enable control turns the switch off nothing
// crosses the terminals, so no strength is imposed on the far net -- it keeps
// its default high-impedance strength.
TEST(StrengthReductionNonresistive, NonconductingTranif1LeavesFarNetStrength) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

}  // namespace
