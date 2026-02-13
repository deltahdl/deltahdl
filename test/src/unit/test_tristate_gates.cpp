#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>

// --- Local types for three-state gates (§28.6) ---

enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

// L = 0 or z, H = 1 or z. Represented as extended values.
enum class Val4Ext : uint8_t {
  kV0 = 0,
  kV1 = 1,
  kX = 2,
  kZ = 3,
  kL = 4,
  kH = 5
};

enum class TristateKind : uint8_t { kBufif0, kBufif1, kNotif0, kNotif1 };

Val4Ext EvalTristateGate(TristateKind kind, Val4 data, Val4 control);
uint64_t ComputeTristateDelay(uint64_t d_rise, uint64_t d_fall, uint64_t d_z,
                              Val4Ext from, Val4Ext to);

// --- Implementations ---

// Helper: compute pass-through value for conducting tristate gate.
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
  // control is x or z — weak / unknown output per Table 28-5.
  if (data == Val4::kV0) return invert ? Val4Ext::kH : Val4Ext::kL;
  if (data == Val4::kV1) return invert ? Val4Ext::kL : Val4Ext::kH;
  return Val4Ext::kX;  // data is x or z
}

uint64_t ComputeTristateDelay(uint64_t d_rise, uint64_t d_fall, uint64_t d_z,
                              Val4Ext from, Val4Ext to) {
  (void)from;  // delay depends only on the destination value
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

// =============================================================
// §28.6: bufif1, bufif0, notif1, and notif0 gates
// =============================================================

// §28.6: Truth tables (Table 28-5)

// bufif0: conducts when control=0
TEST(TristateGates, Bufif0TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      // control=0: pass data through
      {Val4::kV0, Val4::kV0, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kV1},
      {Val4::kX, Val4::kV0, Val4Ext::kX},
      {Val4::kZ, Val4::kV0, Val4Ext::kX},
      // control=1: output z
      {Val4::kV0, Val4::kV1, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kZ},
      {Val4::kX, Val4::kV1, Val4Ext::kZ},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      // control=x: L or H or x
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kX},
      // control=z: same as control=x
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kX},
  };
  for (const auto &c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kBufif0, c.data, c.control),
              c.expected)
        << "Bufif0(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

// bufif1: conducts when control=1
TEST(TristateGates, Bufif1TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kV1},
      // x/z control
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
  };
  for (const auto &c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kBufif1, c.data, c.control),
              c.expected)
        << "Bufif1(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

// notif0: conducts inverted when control=0
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
      // x/z control
      {Val4::kV0, Val4::kX, Val4Ext::kH},
      {Val4::kV1, Val4::kX, Val4Ext::kL},
  };
  for (const auto &c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kNotif0, c.data, c.control),
              c.expected)
        << "Notif0(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

// notif1: conducts inverted when control=1
TEST(TristateGates, Notif1TruthTable) {
  struct Case {
    Val4 data;
    Val4 control;
    Val4Ext expected;
  };
  Case cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kV1},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kV0},
      // x/z control
      {Val4::kV0, Val4::kX, Val4Ext::kH},
      {Val4::kV1, Val4::kX, Val4Ext::kL},
  };
  for (const auto &c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kNotif1, c.data, c.control),
              c.expected)
        << "Notif1(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

// §28.6: Three delays — rise, fall, z; smallest = x.
TEST(TristateGates, ThreeDelaySpecification) {
  // rise
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kV1), 10u);
  // fall
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV1, Val4Ext::kV0), 12u);
  // z
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV1, Val4Ext::kZ), 11u);
  // x = smallest of three
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kX), 10u);
}

// §28.6: "Delays on transitions to H or L shall be treated the same
//  as delays on transitions to x."
TEST(TristateGates, DelayToLOrHSameAsX) {
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kL), 10u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kH), 10u);
}

// §28.6: "These four logic gates shall have one output, one data input,
//  and one control input."
