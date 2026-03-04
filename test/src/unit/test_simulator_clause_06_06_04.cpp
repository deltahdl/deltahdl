#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

static Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < vec.nwords; ++w) {
    vec.words[w].aval = ~uint64_t{0};
    vec.words[w].bval = ~uint64_t{0};
  }
  return vec;
}
static Net MakeTriregNet(Arena& arena, Variable*& var, Strength strength,
                         uint8_t width, uint64_t initial_val) {
  var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, width, initial_val);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.charge_strength = strength;
  net.drivers.push_back(MakeAllZ(arena, width));
  return net;
}

namespace {

TEST(NetResolution, TriregRetainsPrevValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();

  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

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

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

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

  ASSERT_TRUE(sched.HasEvents());
  sched.Run();

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

  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena, &sched);
  ASSERT_TRUE(sched.HasEvents());

  net.drivers[0] = MakeLogic4VecVal(arena, 8, 99);
  net.Resolve(arena, &sched);

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

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CapacitiveNetwork, LargerOverridesSmaller) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 8, 1);
  Net b = MakeTriregNet(arena, var_b, Strength::kSmall, 8, 0);

  PropagateCharge(a, b);
  EXPECT_EQ(var_b->value.ToUint64(), 1u);
  EXPECT_EQ(var_a->value.ToUint64(), 1u);
}

TEST(CapacitiveNetwork, EqualStrengthDifferentValuesToX) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kMedium, 8, 1);
  Net b = MakeTriregNet(arena, var_b, Strength::kMedium, 8, 0);

  PropagateCharge(a, b);

  EXPECT_EQ(var_a->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var_a->value.words[0].bval & 0xFF, 0xFFu);
  EXPECT_EQ(var_b->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var_b->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(CapacitiveNetwork, EqualStrengthSameValueRetained) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kMedium, 8, 55);
  Net b = MakeTriregNet(arena, var_b, Strength::kMedium, 8, 55);

  PropagateCharge(a, b);
  EXPECT_EQ(var_a->value.ToUint64(), 55u);
  EXPECT_EQ(var_b->value.ToUint64(), 55u);
}

TEST(CapacitiveNetwork, OnlyWhenBothCapacitive) {
  Arena arena;
  Variable* var_a = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 8, 1);

  auto* var_b = arena.Create<Variable>();
  var_b->value = MakeLogic4VecVal(arena, 8, 0);
  Net b;
  b.type = NetType::kTrireg;
  b.resolved = var_b;
  b.charge_strength = Strength::kSmall;
  b.drivers.push_back(MakeLogic4VecVal(arena, 8, 77));

  PropagateCharge(a, b);

  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 0u);
}

}  // namespace
