#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UserNettypeStrength, NonUserNettypeStillHonorsStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = false;

  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

TEST(UserNettypeStrength, UserNettypeSingleDriverUsesValueOnly) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 1, Strength::kHighz);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

TEST(UserNettypeStrength, UserNettypeIgnoresStrengthPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 4, 0b1100, Strength::kStrong);
  AddDriver(arena, net, 4, 0b1010, Strength::kWeak);
  net.Resolve(arena);

  // Bits 1,2 conflict -> x = (aval=1, bval=1); bit3=1, bit0=0 (Convention A).
  EXPECT_EQ(sn.var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(UserNettypeStrength, UserNettypeIgnoresStrengthWithThreeDrivers) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 0, Strength::kSupply);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(UserNettypeStrength, UserNettypeConflictKeepsNoStrengthLevels) {
  // Two equally strong, opposing drivers on a user-defined-nettype net. On an
  // ordinary net this conflict would populate a strength range (an ambiguous
  // strength); the nettype net must instead carry no strength levels at all,
  // resolving the conflict as a value only.
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  // Value resolves to x, the strengths having played no part in the outcome.
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);

  // No strength levels appear on either side of the scale.
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(NetStrengthDisjunction, UnambiguousDriversYieldUnambiguousNetStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
}

TEST(NetStrengthDisjunction, ValueZeroDominantDriverRecordsStrengthOnSide0) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kHighz});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kHighz, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(NetStrengthDisjunction, AmbiguousNetStrengthIsRepresentable) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kWeak;
  EXPECT_TRUE(ns.IsAmbiguous());

  NetStrength single;
  single.s0_hi = Strength::kPull;
  single.s0_lo = Strength::kPull;
  EXPECT_FALSE(single.IsAmbiguous());
}

// §28.12 (own text): a net declared with a user-defined nettype shall not have
// strength levels, and any strength associated with its drivers shall be
// ignored. The distinguishing input -- the user-defined-nettype flag -- is
// produced by real §6.6.7 nettype syntax, so this drives the rule through the
// full pipeline (parse, elaborate, lower, run) rather than hand-building a Net.
// A companion ordinary wire, driven by an identical continuous assignment,
// records the driver's (default strong) strength; the nettype net must not.
TEST(UserNettypeStrength, RealSourceNettypeNetRecordsNoStrengthLevels) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net x;\n"
      "  wire [7:0] y;\n"
      "  assign x = 8'hAB;\n"
      "  assign y = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // The nettype net takes the driver value, its strength having played no part.
  auto* xvar = f.ctx.FindVariable("x");
  ASSERT_NE(xvar, nullptr);
  EXPECT_EQ(xvar->value.ToUint64(), 0xABu);

  // §28.12: the user-defined-nettype net carries no strength levels -- both
  // sides of the scale are left at their default (high-impedance) sentinel and
  // the resolved strength is not ambiguous.
  auto* xnet = f.ctx.FindNet("x");
  ASSERT_NE(xnet, nullptr);
  EXPECT_TRUE(xnet->is_user_nettype);
  EXPECT_EQ(xnet->resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(xnet->resolved_strength.IsAmbiguous());

  // Contrast: the ordinary wire, driven identically, does record the
  // continuous assignment's strong drive strength on the value-1 side.
  auto* ynet = f.ctx.FindNet("y");
  ASSERT_NE(ynet, nullptr);
  EXPECT_FALSE(ynet->is_user_nettype);
  EXPECT_EQ(ynet->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(ynet->resolved_strength.s1_lo, Strength::kStrong);
}

TEST(NetStrengthDisjunction, NetStrengthMutationTogglesIsAmbiguous) {
  NetStrength ns;
  EXPECT_FALSE(ns.IsAmbiguous());

  ns.s0_hi = Strength::kLarge;
  ns.s0_lo = Strength::kMedium;
  EXPECT_TRUE(ns.IsAmbiguous());

  ns.s0_lo = Strength::kLarge;
  EXPECT_FALSE(ns.IsAmbiguous());
}

// §28.12 resolves each bit of a net on its own -- the strength of a combined
// signal is a property of the signal on that bit, and a net's bits need not
// resolve alike. A net reports one pair of strength ranges, so the pair has to
// take in every bit: §28.12.2 already has an ambiguous signal's strength be a
// range of levels rather than one level, and that is the shape the pair takes
// where the bits differ.
//
// One driver under (weak0, pull1) holding 2'b01 is what tells the bits apart.
// Bit 0 is driven 1, which the specification puts at pull; bit 1 is driven 0,
// which it puts at weak. So the two bits resolve on two sides at two levels
// from one driver, and a pair read off bit 0 alone says the net drives nothing
// low.
TEST(NetStrengthDisjunction, VectorBitsResolvingUnalikeWidenTheReportedPair) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 2);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 2, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kPull});
  net.Resolve(arena);

  // Bit 0's side, which bit-0-only reporting also reaches.
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  // Bit 1's side, which it does not.
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kWeak);
}

// §28.12: a net whose bits do resolve alike reports what one of them does. The
// same driver and the same specification holding 2'b11 drives both bits 1 at
// pull, so the 0 side is driven by no bit and stays at highz, and the pair does
// not open into a range. Without this case, a reporting rule that widened
// unconditionally -- taking every bit's highz bound in -- would satisfy the
// case above and turn every unambiguous net ambiguous.
TEST(NetStrengthDisjunction, VectorBitsResolvingAlikeReportWhatOneBitDoes) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 2);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 2, 3));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

// §28.12.2: "signals with a value x ... have strength levels consisting of
// subdivisions of both the strength1 and the strength0 parts of the scale of
// strengths". A driver whose value is x therefore puts its own level on both
// sides, and both bounds sit at that level: the level is known even though the
// value is not, so the result is not the range the equal-and-opposite conflict
// produces, which §28.12.2 gives "all the smaller strength levels" as well.
TEST(NetStrengthDisjunction, DriverOfUnknownValueRecordsItsLevelOnBothSides) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  // x = (aval=1, bval=1) on the single bit, driven at pull on both sides.
  auto drv = MakeLogic4Vec(arena, 1);
  drv.words[0].aval = 1;
  drv.words[0].bval = 1;
  net.drivers.push_back(drv);
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  // Both bounds at one level is what §21.2.1.4 renders with a mnemonic rather
  // than with the two digits an ambiguous strength takes.
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

// The negative form: a net no driver reaches keeps every level at high
// impedance. That is the answer the case above used to give as well, so a fix
// has to leave this one alone.
TEST(NetStrengthDisjunction, NetWithNoDriverRecordsNoLevels) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

}  // namespace
