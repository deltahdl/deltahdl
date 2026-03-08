#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
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
                         uint32_t width, uint64_t initial_val) {
  var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, width, initial_val);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.charge_strength = strength;
  net.base_charge_strength = strength;
  net.drivers.push_back(MakeAllZ(arena, width));
  return net;
}

namespace {

// §6.6.4.1: Larger charge strength overrides smaller — value propagates.
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

// §6.6.4.1: Reverse argument order — smaller is first arg.
TEST(CapacitiveNetwork, SmallerFirstArgStillOverridden) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kSmall, 8, 0);
  Net b = MakeTriregNet(arena, var_b, Strength::kLarge, 8, 1);

  PropagateCharge(a, b);
  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 1u);
}

// §6.6.4.1: Equal strength, different values → both x.
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

// §6.6.4.1: Equal strength, same value → retained.
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

// §6.6.4.1: No propagation unless both nets are in capacitive state.
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
  b.base_charge_strength = Strength::kSmall;
  b.drivers.push_back(MakeLogic4VecVal(arena, 8, 77));

  PropagateCharge(a, b);

  EXPECT_EQ(var_a->value.ToUint64(), 1u);
  EXPECT_EQ(var_b->value.ToUint64(), 0u);
}

// §6.6.4.1: Charge strength sharing — smaller net adopts larger's strength.
TEST(CapacitiveNetwork, SmallerAdoptsLargerChargeStrength) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 8, 1);
  Net b = MakeTriregNet(arena, var_b, Strength::kSmall, 8, 1);

  PropagateCharge(a, b);
  EXPECT_EQ(b.charge_strength, Strength::kLarge);
  EXPECT_EQ(a.charge_strength, Strength::kLarge);
}

// §6.6.4.1: DisconnectCharge restores base charge strength.
TEST(CapacitiveNetwork, DisconnectRestoresBaseStrength) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 8, 1);
  Net b = MakeTriregNet(arena, var_b, Strength::kSmall, 8, 1);

  PropagateCharge(a, b);
  EXPECT_EQ(b.charge_strength, Strength::kLarge);

  DisconnectCharge(b);
  EXPECT_EQ(b.charge_strength, Strength::kSmall);
}

// §6.6.4.1: Equal strength propagation does not change charge strength.
TEST(CapacitiveNetwork, EqualStrengthNoChargeStrengthChange) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  Net a = MakeTriregNet(arena, var_a, Strength::kMedium, 8, 1);
  Net b = MakeTriregNet(arena, var_b, Strength::kMedium, 8, 0);

  PropagateCharge(a, b);
  EXPECT_EQ(a.charge_strength, Strength::kMedium);
  EXPECT_EQ(b.charge_strength, Strength::kMedium);
}

// §6.6.4.1: Multi-word vector propagation works correctly.
TEST(CapacitiveNetwork, MultiWordVectorPropagation) {
  Arena arena;
  Variable* var_a = nullptr;
  Variable* var_b = nullptr;
  // Use 128-bit width (2 words).
  Net a = MakeTriregNet(arena, var_a, Strength::kLarge, 128, 0xDEAD);
  Net b = MakeTriregNet(arena, var_b, Strength::kSmall, 128, 0xBEEF);

  PropagateCharge(a, b);
  EXPECT_EQ(var_b->value.ToUint64(), 0xDEADu);
  EXPECT_EQ(var_a->value.ToUint64(), 0xDEADu);
}

}  // namespace
