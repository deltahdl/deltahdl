// §28.16: Gate and net delays

#include <gtest/gtest.h>
#include <algorithm>
#include <cstdint>
#include <initializer_list>

// --- Local types for gate/net delays (§28.16) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

struct DelaySpec {
  uint64_t d1 = 0;    // rise
  uint64_t d2 = 0;    // fall
  uint64_t d3 = 0;    // turn-off (z) or charge decay for trireg
  uint8_t count = 0;  // 0, 1, 2, or 3
};

enum class ChargeDecayState : uint8_t { kIdle, kDecaying, kDone };

uint64_t ComputePropagationDelay(const DelaySpec& spec, Val4 from, Val4 to) {
  if (spec.count == 0) return 0;
  if (spec.count == 1) return spec.d1;
  if (from == to) return 0;
  if (spec.count == 2) {
    switch (to) {
      case Val4::kV1:
        return spec.d1;
      case Val4::kV0:
        return spec.d2;
      case Val4::kZ:
      case Val4::kX:
        return std::min(spec.d1, spec.d2);
    }
  }
  // count == 3
  switch (to) {
    case Val4::kV1:
      return spec.d1;
    case Val4::kV0:
      return spec.d2;
    case Val4::kZ:
      return spec.d3;
    case Val4::kX:
      return std::min({spec.d1, spec.d2, spec.d3});
  }
  return 0;
}

namespace {

// =============================================================
// §28.16: Gate and net delays
// =============================================================
// §28.16: "the default delay shall be zero when no delay
//  specification is given."
TEST(GateNetDelays, DefaultDelayIsZero) {
  DelaySpec spec;
  spec.count = 0;
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 0u);
}

// §28.16: "When one delay value is given, then this value shall be
//  used for all propagation delays."
TEST(GateNetDelays, SingleDelayUsedForAll) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
}

// §28.16: "When two delays are given, the first delay shall specify
//  the rise delay, and the second delay shall specify the fall
//  delay."
TEST(GateNetDelays, TwoDelayRiseAndFall) {
  DelaySpec spec{10, 20, 0, 2};
  // 0→1 = d1 (rise)
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
  // 1→0 = d2 (fall)
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 20u);
}

// §28.16: "The delay when the signal changes to high impedance or
//  to unknown shall be the lesser of the two delay values."
TEST(GateNetDelays, TwoDelayToZAndXIsMinimum) {
  DelaySpec spec{10, 20, 0, 2};
  // *→z = min(d1, d2)
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kZ), 10u);
  // *→x = min(d1, d2)
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
}

// §28.16: Table 28-9 — full three-delay specification.
TEST(GateNetDelays, ThreeDelay0To1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
}

TEST(GateNetDelays, ThreeDelay1To0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayToZIsD3) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kZ), 15u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 15u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kZ), 15u);
}

TEST(GateNetDelays, ThreeDelayToXIsMinOfAll) {
  DelaySpec spec{10, 20, 15, 3};
  // min(10, 20, 15) = 10
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kX), 10u);
}

// §28.16: Table 28-9 — x→0 = d2, x→1 = d1.
TEST(GateNetDelays, ThreeDelayXTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayXTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV1), 10u);
}

// §28.16: Table 28-9 — z→0 = d2, z→1 = d1.
TEST(GateNetDelays, ThreeDelayZTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayZTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV1), 10u);
}

// §28.4: Two delays — "the first delay shall determine the output rise
//  delay, the second delay shall determine the output fall delay, and
//  the smaller of the two delays shall apply to output transitions to x."
TEST(LogicGates, TwoDelayRiseFallAndX) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u);  // rise
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u);  // fall
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);   // min
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);   // min
}

}  // namespace
