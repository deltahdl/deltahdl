// §28.10: pullup and pulldown sources

#include <cstdint>
#include <gtest/gtest.h>

// --- Local types for pullup/pulldown sources (§28.10) ---
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

enum class PullKind : uint8_t { kPullup, kPulldown };

struct PullSourceInfo {
  PullKind kind = PullKind::kPullup;
  bool has_strength0 = false;
  bool has_strength1 = false;
  StrengthLevel strength0 = StrengthLevel::kPull;
  StrengthLevel strength1 = StrengthLevel::kPull;
};

Val4 EvalPullSource(PullKind kind);

StrengthLevel GetPullSourceStrength(const PullSourceInfo &info);

bool PullSourceAcceptsDelaySpec();

Val4 EvalPullSource(PullKind kind) {
  switch (kind) {
  case PullKind::kPullup:
    return Val4::kV1;
  case PullKind::kPulldown:
    return Val4::kV0;
  }
  return Val4::kX;
}

StrengthLevel GetPullSourceStrength(const PullSourceInfo &info) {
  if (info.kind == PullKind::kPullup && info.has_strength1)
    return info.strength1;
  if (info.kind == PullKind::kPulldown && info.has_strength0)
    return info.strength0;
  return StrengthLevel::kPull;
}

bool PullSourceAcceptsDelaySpec() { return false; }

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

} // namespace
