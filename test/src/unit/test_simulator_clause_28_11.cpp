// §28.11: Logic strength modeling

#include <cstdint>
#include <gtest/gtest.h>

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
  return s0 != StrengthLevel::kHighz || s1 != StrengthLevel::kHighz;
}

StrengthSignal CombineUnambiguous(StrengthSignal a, StrengthSignal b) {
  // Effective strength is the maximum of the two strength fields,
  // since for an unambiguous signal one side is always highz.
  auto effective = [](const StrengthSignal &s) -> StrengthLevel {
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
  auto effective = [](const StrengthSignal &s) -> StrengthLevel {
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
  Val4 resolved = Val4::kX;
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
  case StrengthLevel::kStrong:
    return StrengthLevel::kPull;
  case StrengthLevel::kPull:
    return StrengthLevel::kWeak;
  case StrengthLevel::kLarge:
  case StrengthLevel::kWeak:
    return StrengthLevel::kMedium;
  case StrengthLevel::kMedium:
  case StrengthLevel::kSmall:
    return StrengthLevel::kSmall;
  default:
    return StrengthLevel::kHighz;
  }
}

namespace {

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

} // namespace
