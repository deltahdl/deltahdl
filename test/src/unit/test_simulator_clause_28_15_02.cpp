#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Builds a trireg holding `held` on its low bit with every driver at high
// impedance, which is exactly the charge storage state of §28.15.2.
Net MakeChargedTrireg(Arena& arena, uint64_t held, uint32_t width) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, width, held);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < z.nwords; ++w) {
    z.words[w] = {~uint64_t{0}, ~uint64_t{0}};
  }
  net.drivers.push_back(z);
  return net;
}

// §28.15.2: a trireg with no charge strength named in its declaration retains
// its charge at medium strength.
TEST(TriregChargeStrength, DefaultDriveIsMediumStrength) {
  Arena arena;
  Net net = MakeChargedTrireg(arena, 1, 1);  // leave charge_strength defaulted
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kMedium);
}

// §28.15.2: a trireg declared (small) drives its retained value at small
// charge strength. A held 0 places that strength on the zero side only, since
// the charge storage drive carries just the value it retained.
TEST(TriregChargeStrength, SmallDriveStrengthOnHeldZero) {
  Arena arena;
  Net net = MakeChargedTrireg(arena, 0, 1);
  net.charge_strength = Strength::kSmall;
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSmall);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kSmall);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
}

// §28.15.2 edge case: a trireg whose retained charge is unknown is still in the
// charge storage state, so its drive carries the charge strength. The held
// value being ambiguous, that strength appears on both the 0 and 1 sides.
TEST(TriregChargeStrength, UnknownHeldValueDrivesBothSidesAtChargeStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  var->value.words[0] = {0, 1};  // x on the low bit: aval clear, bval set
  Net net;
  net.type = NetType::kTrireg;
  net.charge_strength = Strength::kLarge;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, 1);
  z.words[0] = {~uint64_t{0}, ~uint64_t{0}};  // sole driver at high impedance
  net.drivers.push_back(z);
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kLarge);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kLarge);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kLarge);
}

}  // namespace
