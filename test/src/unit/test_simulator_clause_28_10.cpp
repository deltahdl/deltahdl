#include <gtest/gtest.h>

#include "model_pull_source.h"

namespace {

TEST(PullGates, PullupOutputsOne) {
  EXPECT_EQ(EvalPullSource(PullKind::kPullup), Val4::kV1);
}

TEST(PullGates, PulldownOutputsZero) {
  EXPECT_EQ(EvalPullSource(PullKind::kPulldown), Val4::kV0);
}

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

TEST(PullGates, PullupStrength1Honored) {
  PullSourceInfo info;
  info.kind = PullKind::kPullup;
  info.has_strength1 = true;
  info.strength1 = StrengthLevel::kStrong;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kStrong);
}

TEST(PullGates, PulldownStrength0Honored) {
  PullSourceInfo info;
  info.kind = PullKind::kPulldown;
  info.has_strength0 = true;
  info.strength0 = StrengthLevel::kWeak;
  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kWeak);
}

TEST(PullGates, PullupIgnoresStrength0) {
  PullSourceInfo info;
  info.kind = PullKind::kPullup;
  info.has_strength0 = true;
  info.strength0 = StrengthLevel::kSupply;

  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

TEST(PullGates, PulldownIgnoresStrength1) {
  PullSourceInfo info;
  info.kind = PullKind::kPulldown;
  info.has_strength1 = true;
  info.strength1 = StrengthLevel::kSupply;

  EXPECT_EQ(GetPullSourceStrength(info), StrengthLevel::kPull);
}

TEST(PullGates, NoDelaySpecs) { EXPECT_FALSE(PullSourceAcceptsDelaySpec()); }

}  // namespace
