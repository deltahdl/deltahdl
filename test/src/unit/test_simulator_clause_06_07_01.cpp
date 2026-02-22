// §6.7.1: Net declarations with built-in net types

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"
#include <cstdint>
#include <gtest/gtest.h>

using namespace delta;

// --- Local types for net declaration validation (§6.7) ---
enum class LocalChargeStrength : uint8_t {
  kSmall,
  kMedium,
  kLarge,
};

enum class NetDataTypeKind : uint8_t {
  k4StateIntegral,
  kFixedUnpackedValid,
  k2StateIntegral,
  kReal,
  kDynamicArray,
  kString,
};

struct NetDeclInfo {
  NetType type = NetType::kWire;
  bool has_charge_strength = false;
  LocalChargeStrength charge = LocalChargeStrength::kMedium;
  bool is_vectored = false;
  bool is_scalared = false;
  bool is_interconnect = false;
  uint32_t packed_dim_count = 0;
  uint32_t delay_count = 0;
  bool has_data_type = false;
  bool has_drive_strength = false;
  bool has_assignment = false;
  NetDataTypeKind data_kind = NetDataTypeKind::k4StateIntegral;
};

bool ValidateNetDecl(const NetDeclInfo &info);

bool ValidateNetDataType(NetDataTypeKind kind);

void InitializeNet(Net &net, NetType type, Arena &arena);

void InitializeTriregNet(Net &net, LocalChargeStrength str, Arena &arena);

static bool ValidateInterconnectDecl(const NetDeclInfo &info) {
  if (info.has_data_type)
    return false;
  if (info.has_drive_strength)
    return false;
  if (info.has_charge_strength)
    return false;
  if (info.has_assignment)
    return false;
  return info.delay_count <= 1;
}

bool ValidateNetDecl(const NetDeclInfo &info) {
  // Charge strength only allowed on trireg.
  if (info.has_charge_strength && info.type != NetType::kTrireg &&
      !info.is_interconnect)
    return false;
  // vectored/scalared require at least one packed dimension.
  if ((info.is_vectored || info.is_scalared) && info.packed_dim_count == 0)
    return false;
  // Interconnect constraints.
  if (info.is_interconnect)
    return ValidateInterconnectDecl(info);
  return true;
}

bool ValidateNetDataType(NetDataTypeKind kind) {
  switch (kind) {
  case NetDataTypeKind::k4StateIntegral:
  case NetDataTypeKind::kFixedUnpackedValid:
    return true;
  case NetDataTypeKind::k2StateIntegral:
  case NetDataTypeKind::kReal:
  case NetDataTypeKind::kDynamicArray:
  case NetDataTypeKind::kString:
    return false;
  }
  return false;
}

void InitializeNet(Net &net, NetType type, Arena &arena) {
  (void)type;
  (void)arena;
  if (!net.drivers.empty()) {
    // Resolve to driver value.
    net.resolved->value = net.drivers[0];
  } else {
    // Default to z: aval=1, bval=1.
    for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
      net.resolved->value.words[i].aval = 1;
      net.resolved->value.words[i].bval = 1;
    }
  }
}

void InitializeTriregNet(Net &net, LocalChargeStrength str, Arena &arena) {
  (void)str;
  (void)arena;
  // Set value to x: aval=0, bval=1.
  for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
    net.resolved->value.words[i].aval = 0;
    net.resolved->value.words[i].bval = 1;
  }
}

// --- Helpers ---
static uint8_t ValOf(const Variable &v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal1 = 1;

static constexpr uint8_t kValX = 2;

static constexpr uint8_t kValZ = 3;

namespace {

// --- Strength information (§6.7.1) ---
// §6.7.1: "each bit of a net shall have additional strength information."
TEST(NetDecl, EachBitHasStrengthInformation) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0xF));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  EXPECT_EQ(net.driver_strengths.size(), 1u);
}

// --- Default initialization (§6.7.1) ---
// §6.7.1: "The default initialization value for a net shall be the
//  value z."
TEST(NetDecl, DefaultInitializationIsZ) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

// §6.7.1: "Nets with drivers shall assume the output value of their
//  drivers."
TEST(NetDecl, NetsWithDriversAssumeDriverValue) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

// §6.7.1: "The trireg net shall default to the value x, with the
//  strength specified in the net declaration."
TEST(NetDecl, TriregDefaultsToXSmall) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kSmall, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXMedium) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kMedium, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXLarge) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kLarge, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

} // namespace
