#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// R5 control: the same conflicting Strong/Weak driver pair on a net whose
// is_user_nettype flag is false must still honor strength and return the
// Strong driver's value. Pins down that the R5 bypass is conditioned on the
// flag, not an accidental side effect of the resolve path.
TEST(UserNettypeStrength, NonUserNettypeStillHonorsStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.is_user_nettype = false;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// A single-driver user-nettype net should surface that driver's value whether
// or not an incidental strength entry is present — strength simply plays no
// role in the resolution of a user-defined nettype.
TEST(UserNettypeStrength, UserNettypeSingleDriverUsesValueOnly) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.is_user_nettype = true;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  // Even with highz strength — which the strength-aware path would discard —
  // the user-nettype net must still surface the raw value 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R5 per bit on a multi-bit net: agreeing bits must carry the common value,
// disagreeing bits must become x. If R5 leaked into the per-bit path, the
// strength-aware resolver would have returned the Strong driver's value
// (0b1100) uniformly — the value-only wire fallback yields bit-level x only
// on the two bits where the drivers disagree.
TEST(UserNettypeStrength, UserNettypeIgnoresStrengthPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.is_user_nettype = true;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  // Bit 3: both 1 → 1. Bit 0: both 0 → 0. Bits 1-2: disagree → x.
  EXPECT_EQ(var->value.words[0].aval & 0xFu, 0b1000u);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0b0110u);
}

// R5 across more than two drivers: the pairwise wire-word fold must still
// ignore every driver's strength. A strength-aware resolver would have picked
// the Supply-0 driver as dominant and returned 0; the value-only fold over
// conflicting drivers instead propagates x.
TEST(UserNettypeStrength, UserNettypeIgnoresStrengthWithThreeDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.is_user_nettype = true;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// R1 disjunction — unambiguous branch. After resolving drivers that all carry
// single strength levels, the net's resolved strength must report a single
// level (hi == lo on the value's side, other side unused) and must not read as
// ambiguous.
TEST(NetStrengthDisjunction, UnambiguousDriversYieldUnambiguousNetStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
}

// R1 disjunction — ambiguous branch must be representable. The net-strength
// type has to distinguish a range of levels from a single level; without this,
// §28.12.2+ has no surface on which to record the "strength levels of both
// signals and all the smaller strength levels" outcomes.
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

// R1 exclusivity — a net cannot be in both states at once. The default state
// (all highz, both sides equal) is unambiguous; flipping one side's hi-above-lo
// moves it to the ambiguous state; equalising again returns it to unambiguous.
// Demonstrates the either/or contract the disjunction promises.
TEST(NetStrengthDisjunction, NetStrengthMutationTogglesIsAmbiguous) {
  NetStrength ns;
  EXPECT_FALSE(ns.IsAmbiguous());

  ns.s0_hi = Strength::kLarge;
  ns.s0_lo = Strength::kMedium;
  EXPECT_TRUE(ns.IsAmbiguous());

  ns.s0_lo = Strength::kLarge;
  EXPECT_FALSE(ns.IsAmbiguous());
}

}  // namespace
