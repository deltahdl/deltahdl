#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>

#include "model_gate_logic.h"
enum class Val4Ext : uint8_t {
  kV0 = 0,
  kV1 = 1,
  kX = 2,
  kZ = 3,
  kL = 4,
  kH = 5
};

enum class TristateKind : uint8_t { kBufif0, kBufif1, kNotif0, kNotif1 };

Val4Ext PassGateValue(Val4 data, bool invert) {
  Val4 v = data;
  if (invert) {
    if (v == Val4::kV0)
      v = Val4::kV1;
    else if (v == Val4::kV1)
      v = Val4::kV0;
    else
      v = Val4::kX;
  }
  if (v == Val4::kZ) v = Val4::kX;
  return static_cast<Val4Ext>(v);
}

Val4Ext EvalTristateGate(TristateKind kind, Val4 data, Val4 control) {
  bool invert =
      (kind == TristateKind::kNotif0 || kind == TristateKind::kNotif1);
  Val4 conduct =
      (kind == TristateKind::kBufif0 || kind == TristateKind::kNotif0)
          ? Val4::kV0
          : Val4::kV1;
  Val4 block = (conduct == Val4::kV0) ? Val4::kV1 : Val4::kV0;

  if (control == conduct) return PassGateValue(data, invert);
  if (control == block) return Val4Ext::kZ;
  if (data == Val4::kV0) return invert ? Val4Ext::kH : Val4Ext::kL;
  if (data == Val4::kV1) return invert ? Val4Ext::kL : Val4Ext::kH;
  return Val4Ext::kX;
}

uint64_t ComputeTristateDelay(uint64_t d_rise, uint64_t d_fall, uint64_t d_z,
                              Val4Ext from, Val4Ext to) {
  (void)from;
  switch (to) {
    case Val4Ext::kV1:
      return d_rise;
    case Val4Ext::kV0:
      return d_fall;
    case Val4Ext::kZ:
      return d_z;
    default:
      return std::min({d_rise, d_fall, d_z});
  }
}

namespace {

TEST(TristateGates, Bufif0TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kV1},
      {Val4::kX, Val4::kV0, Val4Ext::kX},
      {Val4::kZ, Val4::kV0, Val4Ext::kX},
      {Val4::kV0, Val4::kV1, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kZ},
      {Val4::kX, Val4::kV1, Val4Ext::kZ},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kX},
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kX},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kBufif0, c.data, c.control),
              c.expected)
        << "Bufif0(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

TEST(TristateGates, Bufif1TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ}, {Val4::kV0, Val4::kV1, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ}, {Val4::kV1, Val4::kV1, Val4Ext::kV1},
      {Val4::kV0, Val4::kX, Val4Ext::kL},  {Val4::kV1, Val4::kX, Val4Ext::kH},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kBufif1, c.data, c.control),
              c.expected)
        << "Bufif1(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

TEST(TristateGates, Notif0TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kV1},
      {Val4::kV1, Val4::kV0, Val4Ext::kV0},
      {Val4::kV0, Val4::kV1, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kH},
      {Val4::kV1, Val4::kX, Val4Ext::kL},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kNotif0, c.data, c.control),
              c.expected)
        << "Notif0(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

TEST(TristateGates, Notif1TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ}, {Val4::kV0, Val4::kV1, Val4Ext::kV1},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ}, {Val4::kV1, Val4::kV1, Val4Ext::kV0},
      {Val4::kV0, Val4::kX, Val4Ext::kH},  {Val4::kV1, Val4::kX, Val4Ext::kL},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kNotif1, c.data, c.control),
              c.expected)
        << "Notif1(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

TEST(TristateGates, DelayToLOrHSameAsX) {
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kL), 10u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kH), 10u);
}

// Three-delay-form slot mapping: each transition direction draws from its
// own slot regardless of the source value, so only the destination drives
// which delay is chosen.
TEST(TristateGates, TransitionToOneUsesRiseDelay) {
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kV0, Val4Ext::kV1), 10u);
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kZ, Val4Ext::kV1), 10u);
}

TEST(TristateGates, TransitionToZeroUsesFallDelay) {
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kV1, Val4Ext::kV0), 20u);
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kZ, Val4Ext::kV0), 20u);
}

TEST(TristateGates, TransitionToZUsesTurnOffDelay) {
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kV0, Val4Ext::kZ), 30u);
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kV1, Val4Ext::kZ), 30u);
}

// Transitions to x take the smallest of the three delays; try several
// orderings so the test doesn't accidentally pass via a fixed slot.
TEST(TristateGates, TransitionToXUsesSmallestOfThree) {
  EXPECT_EQ(ComputeTristateDelay(10, 20, 30, Val4Ext::kV0, Val4Ext::kX), 10u);
  EXPECT_EQ(ComputeTristateDelay(25, 15, 30, Val4Ext::kV0, Val4Ext::kX), 15u);
  EXPECT_EQ(ComputeTristateDelay(25, 30, 5, Val4Ext::kV0, Val4Ext::kX), 5u);
}

// Single-delay form expands to the same value in every slot, so every
// transition direction yields that one delay.
TEST(TristateGates, SingleDelayAppliesToAllTransitions) {
  EXPECT_EQ(ComputeTristateDelay(7, 7, 7, Val4Ext::kV0, Val4Ext::kV1), 7u);
  EXPECT_EQ(ComputeTristateDelay(7, 7, 7, Val4Ext::kV1, Val4Ext::kV0), 7u);
  EXPECT_EQ(ComputeTristateDelay(7, 7, 7, Val4Ext::kV0, Val4Ext::kZ), 7u);
  EXPECT_EQ(ComputeTristateDelay(7, 7, 7, Val4Ext::kV0, Val4Ext::kX), 7u);
}

// Two-delay form: the caller fills the z slot with min(rise, fall) so that
// transitions to both z and x (via the min-of-three rule) resolve to the
// smaller of the two explicit values.
TEST(TristateGates, TwoDelayFormUsesSmallerForXAndZ) {
  uint64_t d_rise = 9, d_fall = 4, d_z = 4;
  EXPECT_EQ(ComputeTristateDelay(d_rise, d_fall, d_z, Val4Ext::kV0,
                                 Val4Ext::kZ),
            4u);
  EXPECT_EQ(ComputeTristateDelay(d_rise, d_fall, d_z, Val4Ext::kV0,
                                 Val4Ext::kX),
            4u);
}

// Absent a delay specification, every slot is zero so no transition
// accrues any propagation delay.
TEST(TristateGates, NoDelaySpecMeansZeroPropagation) {
  EXPECT_EQ(ComputeTristateDelay(0, 0, 0, Val4Ext::kV0, Val4Ext::kV1), 0u);
  EXPECT_EQ(ComputeTristateDelay(0, 0, 0, Val4Ext::kV1, Val4Ext::kZ), 0u);
  EXPECT_EQ(ComputeTristateDelay(0, 0, 0, Val4Ext::kV0, Val4Ext::kX), 0u);
}

}  // namespace
