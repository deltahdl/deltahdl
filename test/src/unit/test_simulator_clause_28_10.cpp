// §28.10: pullup and pulldown sources


// --- Local types for pullup/pulldown sources (§28.10) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.10: pullup and pulldown sources
// =============================================================
// §28.10: "A pullup source shall place a logic value 1 on the nets
//  connected in its terminal list."
TEST(PullGates, PullupOutputsOne) {
  EXPECT_EQ(EvalPullSource(PullKind::kPullup), Val4::kV1);
}

// §28.10: "A pulldown source shall place a logic value 0 on the nets
//  connected in its terminal list."
TEST(PullGates, PulldownOutputsZero) {
  EXPECT_EQ(EvalPullSource(PullKind::kPulldown), Val4::kV0);
}

// §28.10: "The signals that these sources place on nets shall have
//  pull strength in the absence of a strength specification."
TEST(PullGates, DefaultStrengthIsPull) {
  PullSourceInfo info;
  info.kind = PullKind::kPullup;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

TEST(PullGates, PulldownDefaultStrengthIsPull) {
  PullSourceInfo info;
  info.kind = PullKind::kPulldown;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

// §28.10: "If there is a strength1 specification on a pullup source ...
//  the signals shall have the strength specified."
TEST(PullGates, PullupStrength1Honored) {
  PullSourceInfo info;
  info.kind = PullKind::kPullup;
  info.has_strength1 = true;
  info.strength1 = StrengthLevel::kStrong;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kStrong);
}

// §28.10: "If there is a ... strength0 specification on a pulldown
//  source, the signals shall have the strength specified."
TEST(PullGates, PulldownStrength0Honored) {
  PullSourceInfo info;
  info.kind = PullKind::kPulldown;
  info.has_strength0 = true;
  info.strength0 = StrengthLevel::kWeak;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kWeak);
}

// §28.10: "A strength0 specification on a pullup source ... shall
//  be ignored."
TEST(PullGates, PullupIgnoresStrength0) {
  PullSourceInfo info;
  info.kind = PullKind::kPullup;
  info.has_strength0 = true;
  info.strength0 = StrengthLevel::kSupply;
  // strength0 on pullup is ignored, falls back to default pull.
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

// §28.10: "A ... strength1 specification on a pulldown source shall
//  be ignored."
TEST(PullGates, PulldownIgnoresStrength1) {
  PullSourceInfo info;
  info.kind = PullKind::kPulldown;
  info.has_strength1 = true;
  info.strength1 = StrengthLevel::kSupply;
  // strength1 on pulldown is ignored, falls back to default pull.
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

// §28.10:
TEST(PullGates, NoDelaySpecs) { EXPECT_FALSE(PullSourceAcceptsDelaySpec()); }

}  // namespace
