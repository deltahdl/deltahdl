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

// --- Implementations ---

StrengthLevel MapStrengthKeyword0(uint8_t keyword_index) {
  // 0=none, 1=highz, 2=weak, 3=pull, 4=strong, 5=supply
  switch (keyword_index) {
    case 0:
      return StrengthLevel::kHighz;
    case 1:
      return StrengthLevel::kHighz;
    case 2:
      return StrengthLevel::kWeak;
    case 3:
      return StrengthLevel::kPull;
    case 4:
      return StrengthLevel::kStrong;
    case 5:
      return StrengthLevel::kSupply;
    default:
      return StrengthLevel::kHighz;
  }
}

StrengthLevel MapStrengthKeyword1(uint8_t keyword_index) {
  // 0=none, 1=highz, 2=weak, 3=pull, 4=strong, 5=supply
  switch (keyword_index) {
    case 0:
      return StrengthLevel::kHighz;
    case 1:
      return StrengthLevel::kHighz;
    case 2:
      return StrengthLevel::kWeak;
    case 3:
      return StrengthLevel::kPull;
    case 4:
      return StrengthLevel::kStrong;
    case 5:
      return StrengthLevel::kSupply;
    default:
      return StrengthLevel::kHighz;
  }
}

bool ValidateStrengthPair(StrengthLevel s0, StrengthLevel s1) {
  // Both highz is illegal; all other combinations are legal.
  if (s0 == StrengthLevel::kHighz && s1 == StrengthLevel::kHighz) {
    return false;
  }
  return true;
}

StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b) {
  // Effective strength is the maximum of the two strength fields,
  // since for an unambiguous signal one side is always highz.
  auto effective = [](const StrengthSignal& s) -> StrengthLevel {
    return std::max(s.strength0_hi, s.strength1_hi);
  };

  StrengthLevel eff_a = effective(a);
  StrengthLevel eff_b = effective(b);

  if (a.value == b.value) {
    // Like values: result has same value with the greater strength.
    StrengthSignal result;
    result.value = a.value;
    StrengthLevel max_str = std::max(eff_a, eff_b);
    if (a.value == Val4::kV0) {
      result.strength0_hi = max_str;
      result.strength1_hi = StrengthLevel::kHighz;
    } else {
      result.strength0_hi = StrengthLevel::kHighz;
      result.strength1_hi = max_str;
    }
    return result;
  }

  // Unlike values: stronger signal dominates.
  if (eff_a > eff_b) {
    return a;
  } else if (eff_b > eff_a) {
    return b;
  }

  // Equal strength, unlike values: produce x.
  StrengthSignal result;
  result.value = Val4::kX;
  result.strength0_hi = eff_a;
  result.strength1_hi = eff_a;
  return result;
}

StrengthSignal CombineWithWiredLogic(StrengthSignal a, StrengthSignal b,
                                     WiredLogicKind logic) {
  // For different strengths, the stronger signal dominates (same as
  // unambiguous combination). Wired logic only applies when two
  // same-strength opposite-value signals combine.
  auto effective = [](const StrengthSignal& s) -> StrengthLevel {
    return std::max(s.strength0_hi, s.strength1_hi);
  };

  StrengthLevel eff_a = effective(a);
  StrengthLevel eff_b = effective(b);

  // If same value or different strengths, defer to unambiguous rules
  // (like values merge, stronger dominates).
  if (a.value == b.value || eff_a != eff_b) {
    return CombineUnambiguous(a, b);
  }

  // Same strength, opposite values: apply wired logic.
  Val4 resolved;
  if (logic == WiredLogicKind::kAnd) {
    // AND: 1&0=0, 1&1=1, 0&0=0
    if (a.value == Val4::kV1 && b.value == Val4::kV1) {
      resolved = Val4::kV1;
    } else {
      resolved = Val4::kV0;
    }
  } else {
    // OR: 1|0=1, 0|0=0, 1|1=1
    if (a.value == Val4::kV0 && b.value == Val4::kV0) {
      resolved = Val4::kV0;
    } else {
      resolved = Val4::kV1;
    }
  }

  StrengthSignal result;
  result.value = resolved;
  if (resolved == Val4::kV0) {
    result.strength0_hi = eff_a;
    result.strength1_hi = StrengthLevel::kHighz;
  } else {
    result.strength0_hi = StrengthLevel::kHighz;
    result.strength1_hi = eff_a;
  }
  return result;
}

StrengthLevel ReduceNonresistive(StrengthLevel input) {
  // supply → strong; all others unchanged.
  if (input == StrengthLevel::kSupply) {
    return StrengthLevel::kStrong;
  }
  return input;
}

StrengthLevel ReduceResistive(StrengthLevel input) {
  // Per Table 28-8:
  //   supply → pull, strong → pull, pull → weak, large → medium,
  //   weak → medium, medium → small, small → small, highz → highz.
  switch (input) {
    case StrengthLevel::kSupply:
      return StrengthLevel::kPull;
    case StrengthLevel::kStrong:
      return StrengthLevel::kPull;
    case StrengthLevel::kPull:
      return StrengthLevel::kWeak;
    case StrengthLevel::kLarge:
      return StrengthLevel::kMedium;
    case StrengthLevel::kWeak:
      return StrengthLevel::kMedium;
    case StrengthLevel::kMedium:
      return StrengthLevel::kSmall;
    case StrengthLevel::kSmall:
      return StrengthLevel::kSmall;
    case StrengthLevel::kHighz:
      return StrengthLevel::kHighz;
    default:
      return StrengthLevel::kHighz;
  }
}

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
  StrengthSignal sig{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
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
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kStrong), StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesPull) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kPull), StrengthLevel::kPull);
}

TEST(StrengthReduction, NonresistivePassesWeak) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kWeak), StrengthLevel::kWeak);
}

TEST(StrengthReduction, NonresistiveReducesSupplyToStrong) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kSupply), StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesHighz) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kHighz), StrengthLevel::kHighz);
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
