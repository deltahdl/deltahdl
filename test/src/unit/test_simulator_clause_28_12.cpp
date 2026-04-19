#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, EqualStrengthConflictProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, HighzDriverIgnored) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, AllHighzProducesZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// R5: A user-defined nettype net must ignore any driver-level strength. With
// conflicting 1-and-0 drivers whose strengths would normally let the stronger
// one win, the user-nettype path must fall through to value-only wire
// resolution (conflicting known bits → x), not the strength-aware path.
TEST(UserNettypeStrength, UserNettypeIgnoresStrongOverWeak) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.is_user_nettype = true;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  // Strength-aware path would have returned 1 (Strong beats Weak). The
  // value-only wire resolution of 1 against 0 produces x (aval=0, bval=1).
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Mirror of the above with the supply/pull pair to confirm the rule holds
// regardless of which specific strength levels the drivers claim.
TEST(UserNettypeStrength, UserNettypeIgnoresSupplyOverPull) {
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
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Control: the same driver setup on a non-user-nettype net must still honor
// strength. This pins down that the R5 bypass is conditioned on the flag, not
// an accidental side effect of the resolve path.
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

}  // namespace
