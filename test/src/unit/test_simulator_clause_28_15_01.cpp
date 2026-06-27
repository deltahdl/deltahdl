#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

Net MakeUndrivenNet(Arena& arena, NetType type, uint32_t width) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < var->value.nwords; ++w) {
    var->value.words[w].aval = ~uint64_t{0};
    var->value.words[w].bval = ~uint64_t{0};
  }
  Net net;
  net.type = type;
  net.resolved = var;
  return net;
}

Logic4Vec MakeAllZ(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval =
        uint64_t{0};  // canonical Convention A: z = (aval=0, bval=1)
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

bool AllBitsKnown(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return false;
  }
  return true;
}

TEST(Tri0Tri1NetStrengths, Tri0NoDriverProducesZero) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri0, 8);
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0u);
}

TEST(Tri0Tri1NetStrengths, Tri0NoDriverHasPullStrength) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri0, 4);
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, Tri1NoDriverProducesOne) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri1, 8);
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0xFFu);
}

TEST(Tri0Tri1NetStrengths, Tri1NoDriverHasPullStrength) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri1, 4);
  net.Resolve(arena);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, Tri0AllZDriverProducesZero) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri0, 8);
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, Tri1AllZDriverProducesOne) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri1, 8);
  net.drivers.push_back(MakeAllZ(arena, 8));
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0xFFu);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
}

// §28.15.1 qualifies the pulldown/pullup default with "in the absence of an
// overriding source." That qualifier is per bit: where a driver supplies a real
// value the source wins, and only the high-impedance bits are pulled to the
// net-type default. A single driver carrying a mix of driven and z bits
// exercises the FixupTriPull path that applies this rule bit by bit.
TEST(Tri0Tri1NetStrengths, Tri0DrivenBitsOverridePulldownOnUndrivenBits) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri0, 8);
  auto driver = MakeLogic4Vec(arena, 8);
  // Low nibble driven to 1 (aval set, bval clear); high nibble z (aval clear,
  // bval set) per Convention A.
  driver.words[0].aval = 0x0F;
  driver.words[0].bval = 0xF0;
  net.drivers.push_back(driver);
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  // Driven bits keep their 1 value; the undriven bits are pulled down to 0.
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0x0Fu);
}

TEST(Tri0Tri1NetStrengths, Tri1DrivenBitsOverridePullupOnUndrivenBits) {
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri1, 8);
  auto driver = MakeLogic4Vec(arena, 8);
  // Low nibble driven to 0 (both clear); high nibble z (aval clear, bval set)
  // per Convention A.
  driver.words[0].aval = 0x00;
  driver.words[0].bval = 0xF0;
  net.drivers.push_back(driver);
  net.Resolve(arena);
  EXPECT_TRUE(AllBitsKnown(net.resolved->value));
  // Driven bits keep their 0 value; the undriven bits are pulled up to 1.
  EXPECT_EQ(net.resolved->value.ToUint64() & 0xFF, 0xF0u);
}

TEST(Tri0Tri1NetStrengths, Tri0WideUndrivenAllBitsZero) {
  constexpr uint32_t kWidth = 96;
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri0, kWidth);
  net.Resolve(arena);
  ASSERT_GT(net.resolved->value.nwords, 1u);
  for (uint32_t w = 0; w < net.resolved->value.nwords; ++w) {
    uint64_t expected_aval = 0;
    uint64_t expected_bval = 0;
    if (w == net.resolved->value.nwords - 1) {
      uint32_t bits_in_top = kWidth - (net.resolved->value.nwords - 1) * 64;
      uint64_t mask =
          (bits_in_top == 64) ? ~uint64_t{0} : (uint64_t{1} << bits_in_top) - 1;
      EXPECT_EQ(net.resolved->value.words[w].aval & mask, expected_aval);
      EXPECT_EQ(net.resolved->value.words[w].bval & mask, expected_bval);
    } else {
      EXPECT_EQ(net.resolved->value.words[w].aval, expected_aval);
      EXPECT_EQ(net.resolved->value.words[w].bval, expected_bval);
    }
  }
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, Tri1WideUndrivenAllBitsOne) {
  constexpr uint32_t kWidth = 96;
  Arena arena;
  Net net = MakeUndrivenNet(arena, NetType::kTri1, kWidth);
  net.Resolve(arena);
  ASSERT_GT(net.resolved->value.nwords, 1u);
  for (uint32_t w = 0; w < net.resolved->value.nwords; ++w) {
    if (w == net.resolved->value.nwords - 1) {
      uint32_t bits_in_top = kWidth - (net.resolved->value.nwords - 1) * 64;
      uint64_t mask =
          (bits_in_top == 64) ? ~uint64_t{0} : (uint64_t{1} << bits_in_top) - 1;
      EXPECT_EQ(net.resolved->value.words[w].aval & mask, mask);
      EXPECT_EQ(net.resolved->value.words[w].bval & mask, 0u);
    } else {
      EXPECT_EQ(net.resolved->value.words[w].aval, ~uint64_t{0});
      EXPECT_EQ(net.resolved->value.words[w].bval, 0u);
    }
  }
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
}

}  // namespace
