// §28.6: bufif1, bufif0, notif1, and notif0 gates

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>

enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

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
  if (v == Val4::kZ)
    v = Val4::kX;
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

  if (control == conduct)
    return PassGateValue(data, invert);
  if (control == block)
    return Val4Ext::kZ;
  if (data == Val4::kV0)
    return invert ? Val4Ext::kH : Val4Ext::kL;
  if (data == Val4::kV1)
    return invert ? Val4Ext::kL : Val4Ext::kH;
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
  for (const auto &c : cases) {
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
  for (const auto &c : cases) {
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
  for (const auto &c : cases) {
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
  for (const auto &c : cases) {
    EXPECT_EQ(EvalTristateGate(TristateKind::kNotif1, c.data, c.control),
              c.expected)
        << "Notif1(" << static_cast<int>(c.data) << ", "
        << static_cast<int>(c.control) << ")";
  }
}

TEST(TristateGates, ThreeDelaySpecification) {
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kV1), 10u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV1, Val4Ext::kV0), 12u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV1, Val4Ext::kZ), 11u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kX), 10u);
}

TEST(TristateGates, DelayToLOrHSameAsX) {
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kL), 10u);
  EXPECT_EQ(ComputeTristateDelay(10, 12, 11, Val4Ext::kV0, Val4Ext::kH), 10u);
}

} // namespace
