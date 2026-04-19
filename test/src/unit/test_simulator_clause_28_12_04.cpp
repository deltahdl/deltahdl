#include <gtest/gtest.h>

#include "common/arena.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(WiredLogic, WiredAndSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV0);
}

TEST(WiredLogic, WiredOrSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV1);
}

TEST(WiredLogic, WiredAndBothOne) {
  StrengthSignal a{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal b{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV1);
}

TEST(WiredLogic, WiredOrBothZero) {
  StrengthSignal a{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  StrengthSignal b{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV0);
}

// R1 at Net::Resolve: on a wand net, two same-strength drivers with opposite
// values must resolve to AND of their values (0), not to x as a plain wire
// would. Exercises the wired-logic branch of ResolveStrengthBit.
TEST(StrengthResolution, WandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// R2 mirror of the above: on a wor net, same-strength conflict resolves to
// OR of the driver values (1).
TEST(StrengthResolution, WorResolvesSameStrengthConflictToOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §28.12.4 names triand and trior as the tri-state variants subject to the
// same rule; verify the runtime applies wired-logic to these net types too
// rather than falling through to the wire path.
TEST(StrengthResolution, TriandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTriand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, TriorResolvesSameStrengthConflictToOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrior;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R4 at the runtime: when wired-logic can produce an unambiguous result
// (both drivers agree), the agreeing value is returned. Here both wand
// drivers drive 1 at equal strength → result is 1.
TEST(StrengthResolution, WandBothOnesResolveToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WorBothZerosResolveToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §28.12.4 says wired-logic kicks in only when drivers share a strength.
// At unequal strengths §28.12.1's dominance rule still governs — a strong-1
// must beat a weak-0 on a wand net and produce 1, not AND-fold to 0.
TEST(StrengthResolution, WandStrongerDriverDominatesWeaker) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R1 per-bit on multi-bit wand: each bit position resolves independently.
// Drivers 0b1100 and 0b1010 at equal strength combine via AND: bits are
// (1&1)=1, (1&0)=0, (0&1)=0, (0&0)=0 → 0b1000.
TEST(StrengthResolution, WandPerBitAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1000u);
}

// R2 per-bit on multi-bit wor: per-bit OR. 0b1100 OR 0b1010 = 0b1110.
TEST(StrengthResolution, WorPerBitOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

// 4-valued wired-logic edge case: on wand, 0 AND x must resolve to 0 (the
// dominating value in AND), not x as a plain wire would produce. Drives the
// x bit via an x-valued driver (aval=0, bval=1).
TEST(StrengthResolution, WandZeroAndXResolvesToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// Mirror for wor: 1 OR x must resolve to 1.
TEST(StrengthResolution, WorOneOrXResolvesToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
