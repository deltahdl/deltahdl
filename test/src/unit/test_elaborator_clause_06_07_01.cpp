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

namespace {

// --- Interconnect restrictions (§6.7.1) ---
// §6.7.1: "A net declared as an interconnect net shall:
//  — have no data type"
TEST(NetDecl, InterconnectNoDataType) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_data_type = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectWithDimensionsOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

// §6.7.1: "— not specify drive_strength or charge_strength"
TEST(NetDecl, InterconnectNoDriveStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_drive_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectNoChargeStrength) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// §6.7.1: "— not have assignment expressions"
TEST(NetDecl, InterconnectNoAssignment) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.has_assignment = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// §6.7.1: "— specify at most one delay value."
TEST(NetDecl, InterconnectOneDelayOk) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, InterconnectMultipleDelaysError) {
  NetDeclInfo info;
  info.is_interconnect = true;
  info.delay_count = 3;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// --- Valid net data types (§6.7.1) ---
// §6.7.1: "A valid data type for a net shall be one of the following:
//  a) A 4-state integral type"
TEST(NetDecl, ValidNetDataType4StateIntegral) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::k4StateIntegral));
}

// §6.7.1: "b) A fixed-size unpacked array or unpacked structure or union,
//  where each element has a valid data type for a net."
TEST(NetDecl, ValidNetDataTypeFixedUnpacked) {
  EXPECT_TRUE(ValidateNetDataType(NetDataTypeKind::kFixedUnpackedValid));
}

// §6.7.1: 2-state integral is NOT valid for built-in net types.
TEST(NetDecl, InvalidNetDataType2StateIntegral) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::k2StateIntegral));
}

TEST(NetDecl, InvalidNetDataTypeReal) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kReal));
}

TEST(NetDecl, InvalidNetDataTypeDynamicArray) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kDynamicArray));
}

TEST(NetDecl, InvalidNetDataTypeString) {
  EXPECT_FALSE(ValidateNetDataType(NetDataTypeKind::kString));
}

} // namespace
