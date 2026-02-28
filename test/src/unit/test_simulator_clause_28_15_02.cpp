// §28.15.2: trireg strength

// --- Local types for net type strengths (§28.15) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

#include <gtest/gtest.h>

#include "model_strength.h"

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

}  // namespace
