// §28.15.2: trireg strength

#include <cstdint>
#include <gtest/gtest.h>

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
// §28.15.2: trireg strength
// =============================================================
// §28.15.2: "The strength of the drive resulting from a trireg net
//  that is in the charge storage state ... shall be one of these
//  three strengths: large, medium, or small."
TEST(NetStrengths, TriregLargeStrength) {
  EXPECT_EQ(GetTriregChargeStrength(ChargeStrength::kLarge),
            StrengthLevel::kLarge);
}

TEST(NetStrengths, TriregMediumStrength) {
  EXPECT_EQ(GetTriregChargeStrength(ChargeStrength::kMedium),
            StrengthLevel::kMedium);
}

TEST(NetStrengths, TriregSmallStrength) {
  EXPECT_EQ(GetTriregChargeStrength(ChargeStrength::kSmall),
            StrengthLevel::kSmall);
}

// §28.15.2:
TEST(NetStrengths, TriregDefaultIsMedium) {
  EXPECT_EQ(GetTriregDefaultChargeStrength(), ChargeStrength::kMedium);
}

} // namespace
