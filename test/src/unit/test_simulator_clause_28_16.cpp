#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>

#include "helpers_mintymax.h"
#include "model_gate_logic.h"

struct DelaySpec {
  uint64_t d1 = 0;
  uint64_t d2 = 0;
  uint64_t d3 = 0;
  uint8_t count = 0;
};
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

TEST(GateNetDelays, DefaultDelayIsZero) {
  DelaySpec spec;
  spec.count = 0;
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 0u);
}

TEST(GateNetDelays, SingleDelayUsedForAll) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
}

TEST(GateNetDelays, TwoDelayRiseAndFall) {
  DelaySpec spec{10, 20, 0, 2};

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 20u);
}

TEST(GateNetDelays, TwoDelayToZAndXIsMinimum) {
  DelaySpec spec{10, 20, 0, 2};

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kZ), 10u);

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
}

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

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kX), 10u);
}

TEST(GateNetDelays, ThreeDelayXTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayXTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV1), 10u);
}

TEST(GateNetDelays, ThreeDelayZTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayZTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV1), 10u);
}

TEST(LogicGates, TwoDelayRiseFallAndX) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);
}

}
