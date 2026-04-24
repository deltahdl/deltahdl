// §28.11

#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

namespace {

// Table 28-7 fixes the numeric level for every scalar-strength name. The
// production Strength enum is the single source of truth consulted by
// strength-aware net resolution, so verify the enum values directly.
TEST(StrengthLevel, SupplyIsLevel7) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kSupply), 7);
}

TEST(StrengthLevel, StrongIsLevel6) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kStrong), 6);
}

TEST(StrengthLevel, PullIsLevel5) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kPull), 5);
}

TEST(StrengthLevel, LargeIsLevel4) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kLarge), 4);
}

TEST(StrengthLevel, WeakIsLevel3) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kWeak), 3);
}

TEST(StrengthLevel, MediumIsLevel2) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kMedium), 2);
}

TEST(StrengthLevel, SmallIsLevel1) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kSmall), 1);
}

TEST(StrengthLevel, HighzIsLevel0) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kHighz), 0);
}

// The StrengthVal bitfield packs both a strength0 and a strength1 into a
// single byte; they address the two halves of Figure 28-2. The packing must
// round-trip every combination of the eight levels on each side.
TEST(StrengthLevel, StrengthValPacksBothSidesIndependently) {
  StrengthVal sv{};
  sv.s0 = static_cast<uint8_t>(Strength::kPull);
  sv.s1 = static_cast<uint8_t>(Strength::kSupply);
  EXPECT_EQ(sv.s0, 5);
  EXPECT_EQ(sv.s1, 7);
}

}  // namespace
