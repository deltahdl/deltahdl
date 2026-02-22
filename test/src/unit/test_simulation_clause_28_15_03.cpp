// §28.15.3: supply0 and supply1 net strengths

#include <gtest/gtest.h>
#include <cstdint>

// --- Local types for net type strengths (§28.15) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

enum class StrengthLevel : uint8_t {
  kHighz = 0,
  kSmall = 1,
  kMedium = 2,
  kWeak = 3,
  kLarge = 4,
  kPull = 5,
  kStrong = 6,
  kSupply = 7,
};

enum class ChargeStrength : uint8_t { kSmall, kMedium, kLarge };

enum class NetKind : uint8_t {
  kTri0,
  kTri1,
  kTrireg,
  kSupply0,
  kSupply1,
};

struct NetDefaultInfo {
  Val4 value = Val4::kZ;
  StrengthLevel strength = StrengthLevel::kHighz;
};

NetDefaultInfo GetNetDefault(NetKind kind);

StrengthLevel GetTriregChargeStrength(ChargeStrength cs);

ChargeStrength GetTriregDefaultChargeStrength();

NetDefaultInfo GetNetDefault(NetKind kind) {
  switch (kind) {
    case NetKind::kTri0:
      return {Val4::kV0, StrengthLevel::kPull};
    case NetKind::kTri1:
      return {Val4::kV1, StrengthLevel::kPull};
    case NetKind::kTrireg:
      return {Val4::kX, StrengthLevel::kMedium};
    case NetKind::kSupply0:
      return {Val4::kV0, StrengthLevel::kSupply};
    case NetKind::kSupply1:
      return {Val4::kV1, StrengthLevel::kSupply};
  }
  return {};
}

StrengthLevel GetTriregChargeStrength(ChargeStrength cs) {
  switch (cs) {
    case ChargeStrength::kSmall:
      return StrengthLevel::kSmall;
    case ChargeStrength::kMedium:
      return StrengthLevel::kMedium;
    case ChargeStrength::kLarge:
      return StrengthLevel::kLarge;
  }
  return StrengthLevel::kMedium;
}

ChargeStrength GetTriregDefaultChargeStrength() {
  return ChargeStrength::kMedium;
}

namespace {

// =============================================================
// §28.15.3: supply0 and supply1 net strengths
// =============================================================
// §28.15.3: "The supply0 and supply1 net types shall have supply
//  driving strengths."
TEST(NetStrengths, Supply0HasSupplyStrength) {
  auto info = GetNetDefault(NetKind::kSupply0);
  EXPECT_EQ(info.strength, StrengthLevel::kSupply);
}

TEST(NetStrengths, Supply1HasSupplyStrength) {
  auto info = GetNetDefault(NetKind::kSupply1);
  EXPECT_EQ(info.strength, StrengthLevel::kSupply);
}

// §28.15.3:
TEST(NetStrengths, Supply0ValueIsZero) {
  auto info = GetNetDefault(NetKind::kSupply0);
  EXPECT_EQ(info.value, Val4::kV0);
}

// §28.15.3: "The supply1 net type models connections to power
//  supplies."
TEST(NetStrengths, Supply1ValueIsOne) {
  auto info = GetNetDefault(NetKind::kSupply1);
  EXPECT_EQ(info.value, Val4::kV1);
}

}  // namespace
