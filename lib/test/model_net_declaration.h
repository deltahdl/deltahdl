#pragma once

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

inline bool ValidateNetDecl(const NetDeclInfo& info);
inline bool ValidateNetDataType(NetDataTypeKind kind);
inline void InitializeNet(Net& net, NetType type, Arena& arena);
inline void InitializeTriregNet(Net& net, LocalChargeStrength str,
                                Arena& arena);

static inline bool ValidateInterconnectDecl(const NetDeclInfo& info) {
  if (info.has_data_type) return false;
  if (info.has_drive_strength) return false;
  if (info.has_charge_strength) return false;
  if (info.has_assignment) return false;
  return info.delay_count <= 1;
}

inline bool ValidateNetDecl(const NetDeclInfo& info) {
  if (info.has_charge_strength && info.type != NetType::kTrireg &&
      !info.is_interconnect)
    return false;
  if ((info.is_vectored || info.is_scalared) && info.packed_dim_count == 0)
    return false;
  if (info.is_interconnect) return ValidateInterconnectDecl(info);
  return true;
}

inline bool ValidateNetDataType(NetDataTypeKind kind) {
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

inline void InitializeNet(Net& net, NetType type, Arena& arena) {
  (void)type;
  (void)arena;
  if (!net.drivers.empty()) {
    net.resolved->value = net.drivers[0];
  } else {
    for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
      net.resolved->value.words[i].aval = 1;
      net.resolved->value.words[i].bval = 1;
    }
  }
}

inline void InitializeTriregNet(Net& net, LocalChargeStrength str,
                                Arena& arena) {
  (void)str;
  (void)arena;
  for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
    net.resolved->value.words[i].aval = 0;
    net.resolved->value.words[i].bval = 1;
  }
}
