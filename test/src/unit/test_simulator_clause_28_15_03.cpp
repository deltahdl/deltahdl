#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Builds a supply net that is being driven by a single contending source. A net
// is only run through Net::Resolve once it has at least one driver, so the
// driver here is what carries the net into the supply-strength resolution path;
// it deliberately drives the opposite value at full strength so the test can
// confirm the supply rule overrides it.
Net MakeDrivenSupplyNet(Arena& arena, NetType type, uint32_t width,
                        uint64_t driver_val) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, width);
  Net net;
  net.type = type;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, width, driver_val));
  net.driver_strengths.push_back(
      DriverStrength{Strength::kStrong, Strength::kStrong});
  return net;
}

// §28.15.3: a supply0 net models a ground connection and shall present supply
// driving strength. Resolving forces the value to 0 with supply strength on the
// zero side, even against a strong driver pushing the opposite value.
TEST(SupplyNetStrengths, Supply0DrivesZeroAtSupplyStrength) {
  Arena arena;
  Net net = MakeDrivenSupplyNet(arena, NetType::kSupply0, 8, 0xFF);
  net.Resolve(arena);
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kSupply);
}

// §28.15.3: a supply1 net models a power-supply connection and shall present
// supply driving strength. Resolving forces the value to 1 with supply strength
// on the one side, even against a strong driver pushing the opposite value.
TEST(SupplyNetStrengths, Supply1DrivesOneAtSupplyStrength) {
  Arena arena;
  Net net = MakeDrivenSupplyNet(arena, NetType::kSupply1, 8, 0x00);
  net.Resolve(arena);
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0xFFu);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kSupply);
}

// §28.15.3 edge case: the supply rule shall hold across the full width of a
// multiword net. A supply1 net wider than one machine word must carry 1 with
// supply strength in every bit, exercising the per-word fill in the resolver.
TEST(SupplyNetStrengths, Supply1WideNetIsAllOnesAtSupplyStrength) {
  constexpr uint32_t kWidth = 96;
  Arena arena;
  Net net = MakeDrivenSupplyNet(arena, NetType::kSupply1, kWidth, 0x00);
  net.Resolve(arena);
  const auto& value = net.resolved->value;
  ASSERT_GT(value.nwords, 1u);
  for (uint32_t w = 0; w < value.nwords; ++w) {
    uint64_t mask = ~uint64_t{0};
    if (w == value.nwords - 1) {
      uint32_t bits_in_top = kWidth - (value.nwords - 1) * 64;
      mask =
          (bits_in_top == 64) ? ~uint64_t{0} : (uint64_t{1} << bits_in_top) - 1;
    }
    EXPECT_EQ(value.words[w].aval & mask, mask);
    EXPECT_EQ(value.words[w].bval & mask, 0u);
  }
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kSupply);
}

}  // namespace
