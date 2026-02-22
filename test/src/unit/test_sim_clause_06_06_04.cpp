// §6.6.4: Trireg net

#include <gtest/gtest.h>
#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

// --- §6.6.4: Trireg charge retention ---
TEST(NetResolution, TriregRetainsPrevValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  // First set the variable to a known value (simulating previous driven state).
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  // All drivers go to Z — trireg should retain value 42.
  auto z_drv = MakeLogic4Vec(arena, 8);
  z_drv.words[0].aval = ~uint64_t{0};
  z_drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(z_drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NetResolution, TriregDrivenNormally) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  // Non-Z driver overrides previous value.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// --- §6.6.4.2: Charge decay ---
TEST(ChargeDecay, DecayChangesValueToX) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  // Decay event should be scheduled.
  ASSERT_TRUE(sched.HasEvents());
  sched.Run();
  // Value should now be all-x (aval=0, bval=0xFF for 8 bits).
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(ChargeDecay, NoDecayWhenDecayTicksZero) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 0;
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ChargeDecay, DecayCancelledWhenDriverReturns) {
  Arena arena;
  Scheduler sched(arena);
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 100;
  // First: all drivers Z — schedules decay.
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());
  // Then: driver returns with value 99 — cancels decay.
  net.drivers[0] = MakeLogic4VecVal(arena, 8, 99);
  net.Resolve(arena, &sched);
  // Run scheduler — the stale decay event should be a no-op.
  sched.Run();
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ChargeDecay, NoDecayScheduledWithoutScheduler) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.decay_ticks = 50;
  net.drivers.push_back(MakeAllZ(arena, 8));
  // No scheduler passed — should not crash, value retained.
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// --- §6.6.4.1: Capacitive network propagation ---
TEST(CapacitiveNetwork, LargerOverridesSmaller) {
  Arena arena;
  auto* var_a = arena.Create<Variable>();
  var_a->value = MakeLogic4VecVal(arena, 8, 1);
  Net a;
  a.type = NetType::kTrireg;
  a.resolved = var_a;
  a.charge_strength = Strength::kLarge;
  a.drivers.push_back(MakeAllZ(arena, 8));

  auto* var_b = arena.Create<Variable>();
  var_b->value = MakeLogic4VecVal(arena, 8, 0);
  Net b;
  b.type = NetType::kTrireg;
  b.resolved = var_b;
  b.charge_strength = Strength::kSmall;
  b.drivers.push_back(MakeAllZ(arena, 8));

  PropagateCharge(a, b);
  EXPECT_EQ(var_b->value.ToUint64(), 1u);
  EXPECT_EQ(var_a->value.ToUint64(), 1u);
}

TEST(CapacitiveNetwork, EqualStrengthDifferentValuesToX) {
  Arena arena;
  auto* var_a = arena.Create<Variable>();
  var_a->value = MakeLogic4VecVal(arena, 8, 1);
  Net a;
  a.type = NetType::kTrireg;
  a.resolved = var_a;
  a.charge_strength = Strength::kMedium;
  a.drivers.push_back(MakeAllZ(arena, 8));

  auto* var_b = arena.Create<Variable>();
  var_b->value = MakeLogic4VecVal(arena, 8, 0);
  Net b;
  b.type = NetType::kTrireg;
  b.resolved = var_b;
  b.charge_strength = Strength::kMedium;
  b.drivers.push_back(MakeAllZ(arena, 8));

  PropagateCharge(a, b);
  // Both should be x (aval=0, bval=0xFF for 8 bits).
  EXPECT_EQ(var_a->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var_a->value.words[0].bval & 0xFF, 0xFFu);
  EXPECT_EQ(var_b->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var_b->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(CapacitiveNetwork, EqualStrengthSameValueRetained) {
  Arena arena;
  auto* var_a = arena.Create<Variable>();
  var_a->value = MakeLogic4VecVal(arena, 8, 55);
  Net a;
  a.type = NetType::kTrireg;
  a.resolved = var_a;
  a.charge_strength = Strength::kMedium;
  a.drivers.push_back(MakeAllZ(arena, 8));

  auto* var_b = arena.Create<Variable>();
  var_b->value = MakeLogic4VecVal(arena, 8, 55);
  Net b;
  b.type = NetType::kTrireg;
  b.resolved = var_b;
  b.charge_strength = Strength::kMedium;
  b.drivers.push_back(MakeAllZ(arena, 8));

  PropagateCharge(a, b);
  EXPECT_EQ(var_a->value.ToUint64(), 55u);
  EXPECT_EQ(var_b->value.ToUint64(), 55u);
}

TEST(CapacitiveNetwork, OnlyWhenBothCapacitive) {
  Arena arena;
  auto* var_a = arena.Create<Variable>();
  var_a->value = MakeLogic4VecVal(arena, 8, 1);
  Net a;
  a.type = NetType::kTrireg;
  a.resolved = var_a;
  a.charge_strength = Strength::kLarge;
  a.drivers.push_back(MakeAllZ(arena, 8));  // Capacitive.

  auto* var_b = arena.Create<Variable>();
  var_b->value = MakeLogic4VecVal(arena, 8, 0);
  Net b;
  b.type = NetType::kTrireg;
  b.resolved = var_b;
  b.charge_strength = Strength::kSmall;
  b.drivers.push_back(MakeLogic4VecVal(arena, 8, 77));  // Actively driven.

  PropagateCharge(a, b);
  // B is actively driven, no propagation should occur.
  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 0u);
}

}  // namespace
