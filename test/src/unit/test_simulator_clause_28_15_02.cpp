#include <gtest/gtest.h>

#include "model_net_default.h"

namespace {

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

TEST(NetStrengths, TriregDefaultIsMedium) {
  EXPECT_EQ(GetTriregDefaultChargeStrength(), ChargeStrength::kMedium);
}

}  // namespace
