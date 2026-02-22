// §6.7: Net declarations

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

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

bool ValidateNetDecl(const NetDeclInfo& info);

bool ValidateNetDataType(NetDataTypeKind kind);

void InitializeNet(Net& net, NetType type, Arena& arena);

void InitializeTriregNet(Net& net, LocalChargeStrength str, Arena& arena);

static bool ValidateInterconnectDecl(const NetDeclInfo& info) {
  if (info.has_data_type) return false;
  if (info.has_drive_strength) return false;
  if (info.has_charge_strength) return false;
  if (info.has_assignment) return false;
  return info.delay_count <= 1;
}

bool ValidateNetDecl(const NetDeclInfo& info) {
  // Charge strength only allowed on trireg.
  if (info.has_charge_strength && info.type != NetType::kTrireg &&
      !info.is_interconnect)
    return false;
  // vectored/scalared require at least one packed dimension.
  if ((info.is_vectored || info.is_scalared) && info.packed_dim_count == 0)
    return false;
  // Interconnect constraints.
  if (info.is_interconnect) return ValidateInterconnectDecl(info);
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

void InitializeNet(Net& net, NetType type, Arena& arena) {
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

void InitializeTriregNet(Net& net, LocalChargeStrength str, Arena& arena) {
  (void)str;
  (void)arena;
  // Set value to x: aval=0, bval=1.
  for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
    net.resolved->value.words[i].aval = 0;
    net.resolved->value.words[i].bval = 1;
  }
}

namespace {

// =============================================================
// §6.7: Net declarations
// =============================================================
// --- Charge strength (§6.7, footnote 16) ---
// §6.7:
TEST(NetDecl, ChargeStrengthOnlyWithTrireg) {
  NetDeclInfo info;
  info.type = NetType::kTrireg;
  info.has_charge_strength = true;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnWireIsError) {
  NetDeclInfo info;
  info.type = NetType::kWire;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ChargeStrengthOnWandIsError) {
  NetDeclInfo info;
  info.type = NetType::kWand;
  info.has_charge_strength = true;
  EXPECT_FALSE(ValidateNetDecl(info));
}

// --- vectored/scalared (§6.7, footnote 16) ---
// §6.7: "When the vectored or scalared keyword is used, there shall be
//  at least one packed dimension."
TEST(NetDecl, VectoredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, VectoredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredRequiresPackedDimension) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

}  // namespace
