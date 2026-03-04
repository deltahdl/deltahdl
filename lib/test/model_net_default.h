#pragma once

#include <cstdint>

#include "model_strength.h"
#include "model_val4.h"

// --- Local types for net default values and strengths (§28.15) ---

enum class NetKind : uint8_t {
  kWire,
  kTri,
  kTri0,
  kTri1,
  kWand,
  kWor,
  kTriand,
  kTrior,
  kTrireg,
  kSupply0,
  kSupply1,
};

struct NetDefaultInfo {
  Val4 value = Val4::kX;
  StrengthLevel strength = StrengthLevel::kHighz;
};

inline NetDefaultInfo GetNetDefault(NetKind kind) {
  NetDefaultInfo info;
  switch (kind) {
    case NetKind::kTri0:
      info.value = Val4::kV0;
      info.strength = StrengthLevel::kPull;
      break;
    case NetKind::kTri1:
      info.value = Val4::kV1;
      info.strength = StrengthLevel::kPull;
      break;
    case NetKind::kSupply0:
      info.value = Val4::kV0;
      info.strength = StrengthLevel::kSupply;
      break;
    case NetKind::kSupply1:
      info.value = Val4::kV1;
      info.strength = StrengthLevel::kSupply;
      break;
    default:
      info.value = Val4::kZ;
      info.strength = StrengthLevel::kHighz;
      break;
  }
  return info;
}

enum class ChargeStrength : uint8_t {
  kSmall,
  kMedium,
  kLarge,
};

inline StrengthLevel GetTriregChargeStrength(ChargeStrength cs) {
  switch (cs) {
    case ChargeStrength::kLarge:
      return StrengthLevel::kLarge;
    case ChargeStrength::kMedium:
      return StrengthLevel::kMedium;
    case ChargeStrength::kSmall:
      return StrengthLevel::kSmall;
  }
  return StrengthLevel::kMedium;
}

inline ChargeStrength GetTriregDefaultChargeStrength() {
  return ChargeStrength::kMedium;
}
