#include <gtest/gtest.h>

#include "common/arena.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// R2 at Net::Resolve: two drivers of equal Strong strength with opposite
// values on a plain wire must resolve to x. The runtime cannot track the
// strength range described in §28.12.2; we verify only the value-level
// component of the rule (aval=0, bval=1 → x).
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

// R2 at the reference model: CombineUnambiguous on two equal-Pull drivers
// with opposite values must produce x. Mirrors the runtime test above at the
// model layer so a divergence between model and resolver would be caught.
TEST(StrengthCombine, EqualStrengthOppositeValueProducesX) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

// R2 at a different strength level in the model: two Weak drivers with
// opposite values must also produce x. Complements the Pull case above to
// confirm R2 is ordinal, not tied to Pull specifically.
TEST(StrengthCombine, EqualWeakOppositeValueProducesX) {
  StrengthSignal weak_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kWeak};
  StrengthSignal weak_zero{Val4::kV0, StrengthLevel::kWeak,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(weak_one, weak_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

// R2 at the top of the driving-strength scale: two Supply drivers with
// opposite values must produce x. Guards against a special-case in the
// resolver that treats Supply as unconditionally dominant.
TEST(StrengthResolution, EqualSupplyConflictProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// R2 applies per bit on a multi-bit net. Drivers of equal strength with
// values 0xF0 and 0x0F conflict on every bit; the resolver must produce x
// across all eight bits rather than a merged bitwise value.
TEST(StrengthResolution, EqualStrengthConflictPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
}

// R2 edge case: on a multi-bit net, bits where both drivers agree must not
// become x. Drivers at equal strength with values 0b1100 and 0b1010 agree on
// the high and low bits (1 and 0 respectively) and conflict on the middle
// two. The agreeing bits must carry the common value; the conflicting bits
// must be x.
TEST(StrengthResolution, EqualStrengthPartialConflictPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  // High bit: both 1 → aval=1, bval=0. Low bit: both 0 → aval=0, bval=0.
  // Middle two bits: conflict → aval=0, bval=1 (x).
  EXPECT_EQ(var->value.words[0].aval & 0xFu, 0b1000u);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0b0110u);
}

}  // namespace
