#include <gtest/gtest.h>

#include <cstdint>

// --- Local types for strength modeling (§28.11-§28.14) ---

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

enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

// A strength signal carries a value and a range of strength levels.
// For unambiguous signals, lo == hi. For ambiguous, lo < hi.
struct StrengthSignal {
  Val4 value = Val4::kZ;
  StrengthLevel strength0_hi = StrengthLevel::kHighz;
  StrengthLevel strength1_hi = StrengthLevel::kHighz;
};

enum class WiredLogicKind : uint8_t { kNone, kAnd, kOr };

StrengthLevel MapStrengthKeyword0(uint8_t keyword_index);
StrengthLevel MapStrengthKeyword1(uint8_t keyword_index);
bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1);
StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b);
StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                     WiredLogicKind logic);
StrengthLevel ReduceNonresistive(StrengthLevel input);
StrengthLevel ReduceResistive(StrengthLevel input);

// =============================================================
// §28.11: Logic strength modeling
// =============================================================

// §28.11: Table 28-7 — strength level mapping.
TEST(StrengthModel, SupplyIsLevel7) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kSupply), 7);
}

TEST(StrengthModel, StrongIsLevel6) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kStrong), 6);
}

TEST(StrengthModel, PullIsLevel5) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kPull), 5);
}

TEST(StrengthModel, LargeIsLevel4) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kLarge), 4);
}

TEST(StrengthModel, WeakIsLevel3) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kWeak), 3);
}

TEST(StrengthModel, MediumIsLevel2) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kMedium), 2);
}

TEST(StrengthModel, SmallIsLevel1) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kSmall), 1);
}

TEST(StrengthModel, HighzIsLevel0) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kHighz), 0);
}

// §28.11: "(highz0, highz1) and (highz1, highz0) shall be
//  considered illegal."
TEST(StrengthModel, BothHighzIsIllegal) {
  EXPECT_FALSE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kHighz));
}

// §28.11: Other combinations are legal.
TEST(StrengthModel, StrongStrongIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kStrong));
}

TEST(StrengthModel, StrongHighz1IsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kHighz));
}

TEST(StrengthModel, Highz0StrongIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kStrong));
}

// =============================================================
// §28.12.1: Combined signals of unambiguous strength
// =============================================================

// §28.12.1: "If two or more signals of unequal strength combine ...
//  the stronger signal shall dominate."
TEST(StrengthCombine, StrongerSignalDominates) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal weak_zero{Val4::kV0, StrengthLevel::kWeak,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(strong_one, weak_zero);
  EXPECT_EQ(result.value, Val4::kV1);
}

// §28.12.1: "The combination of two or more signals of like value
//  shall result in the same value with the greater of all the
//  strengths."
TEST(StrengthCombine, LikeValueTakesGreaterStrength) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result = CombineUnambiguous(pull_one, strong_one);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

// §28.12.1: "The combination of signals identical in strength and
//  value shall result in the same signal."
TEST(StrengthCombine, IdenticalSignalsUnchanged) {
  StrengthSignal sig{Val4::kV0, StrengthLevel::kPull,
                     StrengthLevel::kHighz};
  auto result = CombineUnambiguous(sig, sig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
}

// §28.12.1: Equal strength, unlike values (no wired logic) → x.
TEST(StrengthCombine, EqualStrengthOppositeValueProducesX) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

// =============================================================
// §28.12.4: Wired logic net types
// =============================================================

// §28.12.4: "triand, wand ... shall resolve conflicts when multiple
//  drivers have the same strength. ... treating signals as inputs
//  of logic functions."

// Wired AND: 1 AND 0 = 0
TEST(WiredLogic, WiredAndSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV0);
}

// Wired OR: 1 OR 0 = 1
TEST(WiredLogic, WiredOrSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV1);
}

// Wired AND: both 1 = 1
TEST(WiredLogic, WiredAndBothOne) {
  StrengthSignal a{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal b{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV1);
}

// Wired OR: both 0 = 0
TEST(WiredLogic, WiredOrBothZero) {
  StrengthSignal a{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  StrengthSignal b{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV0);
}

// =============================================================
// §28.13: Strength reduction by nonresistive devices
// =============================================================

// §28.13: "nmos, pmos, and cmos switches shall pass the strength
//  from the data input to the output, except that a supply strength
//  shall be reduced to a strong strength."
TEST(StrengthReduction, NonresistivePassesStrong) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kStrong),
            StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesPull) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kPull), StrengthLevel::kPull);
}

TEST(StrengthReduction, NonresistivePassesWeak) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kWeak), StrengthLevel::kWeak);
}

TEST(StrengthReduction, NonresistiveReducesSupplyToStrong) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kSupply),
            StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesHighz) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kHighz),
            StrengthLevel::kHighz);
}

// =============================================================
// §28.14: Strength reduction by resistive devices
// =============================================================

// §28.14: Table 28-8 — strength reduction rules.
TEST(StrengthReduction, ResistiveSupplyToPull) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kSupply), StrengthLevel::kPull);
}

TEST(StrengthReduction, ResistiveStrongToPull) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kStrong), StrengthLevel::kPull);
}

TEST(StrengthReduction, ResistivePullToWeak) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kPull), StrengthLevel::kWeak);
}

TEST(StrengthReduction, ResistiveLargeToMedium) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kLarge), StrengthLevel::kMedium);
}

TEST(StrengthReduction, ResistiveWeakToMedium) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kWeak), StrengthLevel::kMedium);
}

TEST(StrengthReduction, ResistiveMediumToSmall) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kMedium), StrengthLevel::kSmall);
}

TEST(StrengthReduction, ResistiveSmallToSmall) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kSmall), StrengthLevel::kSmall);
}

TEST(StrengthReduction, ResistiveHighzToHighz) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kHighz), StrengthLevel::kHighz);
}
