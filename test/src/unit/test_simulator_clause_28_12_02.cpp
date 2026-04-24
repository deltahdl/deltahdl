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

// §28.12.2 R1 strength-preservation half: when equal-strength opposite-value
// signals collide, the x result shall carry the strength levels of both
// inputs and all smaller levels. In the hi-only range encoding (implicit
// lower bound of kHighz) that means strength0_hi and strength1_hi both
// equal the shared input level. Distinct from the value-only tests above,
// this pins down the range half of the rule that the runtime cannot check.
TEST(StrengthCombine, EqualStrengthConflictCarriesStrengthRange) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
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

// §28.12.2 ambig+ambig rule: combining two x-valued signals whose strength
// ranges already overlap must widen to the union of the inputs. Here both
// inputs are x with range HiZ..Weak on both sides, so the result must match.
TEST(StrengthCombine, AmbiguousSameRangePreserved) {
  StrengthSignal a{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal b{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  auto result = CombineAmbiguous(a, b);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kWeak);
}

// §28.12.2 ambig+ambig rule: the resulting range shall include the strength
// levels in both component signals. When one input is x with a weak range
// and the other is x with a pull range, the result must carry the wider
// pull range on both sides so the inputs' levels are still included.
TEST(StrengthCombine, AmbiguousWidensToMaxPerSide) {
  StrengthSignal weak_x{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal pull_x{Val4::kX, StrengthLevel::kPull, StrengthLevel::kPull};
  auto result = CombineAmbiguous(weak_x, pull_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
}

// §28.12.2 ambig+ambig rule modeled after Figure 28-9's 35x example: an
// ambiguous signal carrying strength on the strength1 side only (analogue
// of an H range) combined with one carrying strength on the strength0 side
// only (analogue of an L range) yields x with both sides of the combined
// range populated by the component extremes.
TEST(StrengthCombine, AmbiguousOppositeSidesUnion) {
  StrengthSignal pull_h{Val4::kX, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal weak_l{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kHighz};
  auto result = CombineAmbiguous(pull_h, weak_l);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
}

// §28.12.2 ambig+ambig rule: the range extends on each side independently.
// Combining a strong-x with a supply-x must produce supply-x on both sides
// because supply is the larger of the per-side levels.
TEST(StrengthCombine, AmbiguousSupplyDominatesStrongPerSide) {
  StrengthSignal strong_x{Val4::kX, StrengthLevel::kStrong,
                          StrengthLevel::kStrong};
  StrengthSignal supply_x{Val4::kX, StrengthLevel::kSupply,
                          StrengthLevel::kSupply};
  auto result = CombineAmbiguous(strong_x, supply_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
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

// §28.12.2 R1 edge case: R1's equal-strength-conflict-to-x rule shall still
// apply when a weaker third driver is present. The Strong pair conflicts and
// should resolve to x; the Weak driver is dominated under §28.12.1 and must
// not rescue the bit to a known value.
TEST(StrengthResolution, EqualStrengthConflictWithWeakerDriverStillProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// §28.12.2 R2 edge case: folding three ambiguous-strength signals pairwise
// must still yield a result whose per-side range includes every component's
// level. Inputs have Weak, Pull, and Strong ranges on both sides — the fold
// must carry Strong on each side since that is the max across all three.
TEST(StrengthCombine, AmbiguousThreeSignalsFoldPreservesRange) {
  StrengthSignal weak_x{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal pull_x{Val4::kX, StrengthLevel::kPull, StrengthLevel::kPull};
  StrengthSignal strong_x{Val4::kX, StrengthLevel::kStrong,
                          StrengthLevel::kStrong};
  auto result =
      CombineAmbiguous(CombineAmbiguous(weak_x, pull_x), strong_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

}  // namespace
