// §28.15.3: supply0 and supply1 net strengths

// --- Local types for net type strengths (§28.15) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

#include <gtest/gtest.h>

#include "model_strength.h"

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
