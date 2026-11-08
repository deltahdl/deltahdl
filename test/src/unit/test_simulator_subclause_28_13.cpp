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

Strength ToStrength(StrengthLevel level) {
  return static_cast<Strength>(static_cast<uint8_t>(level));
}

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

TEST(StrengthReductionNonresistive, NonconductingTranif1LeavesFarNetStrength) {
  auto r =
      ResolveAcrossBidir(BidirSwitchKind::kTranif1, {0, 0}, Strength::kSupply);
  EXPECT_EQ(ValOf(*r.nets.vb), kValZ);
  EXPECT_EQ(r.b_strength.s1_hi, Strength::kHighz);
}

TEST(StrengthReductionNonresistive, AStrengthChangeOfTheDataInputIsPassedOn) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg en = 0;\n"
      "  wire d, y;\n"
      "  assign (weak0, weak1) d = 1'b1;\n"
      "  assign d = en ? 1'b1 : 1'bz;\n"
      "  nmos (y, d, 1'b1);\n"
      "  initial #1 en = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindNet("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(y->resolved_strength.s1_hi, Strength::kStrong);
}

}  // namespace
