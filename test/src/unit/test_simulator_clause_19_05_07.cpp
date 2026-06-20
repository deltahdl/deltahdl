#include <gtest/gtest.h>

#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// Effective type helpers used across the value-resolution tests.
CoverpointEffectiveType Unsigned(uint32_t width) { return {width, false}; }
CoverpointEffectiveType Signed(uint32_t width) { return {width, true}; }

// LRM 19.5.7 a: with no coverpoint type the effective type of e is its
// self-determined type; with a coverpoint type it is that type.
TEST(ValueResolution, EffectiveTypeSelectsCoverpointTypeWhenPresent) {
  CoverpointEffectiveType self = Signed(8);
  CoverpointEffectiveType cp_type = Unsigned(3);

  CoverpointEffectiveType no_type =
      CoverageDB::EffectiveCoverpointType(false, cp_type, self);
  EXPECT_EQ(no_type.width, 8u);
  EXPECT_TRUE(no_type.is_signed);

  CoverpointEffectiveType with_type =
      CoverageDB::EffectiveCoverpointType(true, cp_type, self);
  EXPECT_EQ(with_type.width, 3u);
  EXPECT_FALSE(with_type.is_signed);
}

// LRM 19.5.7 b: a bin value is statically cast to the effective type — reduced
// to its width and reinterpreted with the type's signedness.
TEST(ValueResolution, StaticCastToEffectiveType) {
  // 15 does not fit bit[2:0]; the cast keeps the low 3 bits -> 7.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Unsigned(3)), 7);
  // For a signed 3-bit type the high bit is a sign bit: 7 -> -1, 15 -> -1.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(7, Signed(3)), -1);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(15, Signed(3)), -1);
  // An in-range value is unchanged.
  EXPECT_EQ(CoverageDB::CastToEffectiveType(3, Signed(3)), 3);
  EXPECT_EQ(CoverageDB::CastToEffectiveType(-1, Signed(3)), -1);
}

// LRM 19.5.7 b, condition 1: an unsigned effective type with a negative signed
// bin value warns.
TEST(ValueResolution, UnsignedEffectiveTypeWarnsOnNegativeSignedValue) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, /*value_is_signed=*/true,
                                        /*value_has_xz=*/false,
                                        /*is_wildcard=*/false, Unsigned(3)),
            BinValueResolution::kUnsignedNegative);
  // A negative value is fine for a signed effective type that can hold it.
  EXPECT_EQ(CoverageDB::ResolveBinValue(-1, true, false, false, Signed(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7 b, condition 2: a value the effective type cannot express warns
// because the cast changes it.
TEST(ValueResolution, OutOfRangeValueWarnsBecauseCastChangesIt) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(15, false, false, false, Unsigned(3)),
            BinValueResolution::kValueChanged);
  EXPECT_EQ(CoverageDB::ResolveBinValue(5, false, false, false, Signed(3)),
            BinValueResolution::kValueChanged);
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, false, false, Unsigned(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7 b, condition 3 and the wildcard preamble: a value with x/z bits
// warns, except for a wildcard bin whose unknown bits are treated as 0/1.
TEST(ValueResolution, UnknownBitsWarnExceptForWildcardBins) {
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, /*value_has_xz=*/true,
                                        /*is_wildcard=*/false, Unsigned(3)),
            BinValueResolution::kUnknownBits);
  EXPECT_EQ(CoverageDB::ResolveBinValue(3, false, /*value_has_xz=*/true,
                                        /*is_wildcard=*/true, Unsigned(3)),
            BinValueResolution::kOk);
}

// LRM 19.5.7, first warning bullet: a singleton value that warns does not
// participate in the bin.
TEST(ValueResolution, WarnedSingletonDoesNotParticipate) {
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(BinValueResolution::kOk));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kUnsignedNegative));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      BinValueResolution::kValueChanged));
  EXPECT_FALSE(
      CoverageDB::SingletonValueParticipates(BinValueResolution::kUnknownBits));
}

// LRM 19.5.7, second range bullet: a range whose endpoint carries x/z bits, or
// whose values would all warn, drops out entirely.
TEST(ValueResolution, RangeDropsWhenEndpointUnknownOrAllValuesWarn) {
  // x/z endpoint removes the range (non-wildcard).
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/false},
                                  Unsigned(3))
          .empty());
  // [6:10] under signed bit[2:0] (domain -4..3) has no expressible value.
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Signed(3))
          .empty());
}

// LRM 19.5.7, third range bullet: a range with at least one non-warning value
// becomes the intersection of its values with the effective type's domain.
TEST(ValueResolution, RangeBecomesIntersectionWithEffectiveDomain) {
  // [6:10] under bit[2:0] (0..7) -> [6:7].
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{6, 7}));
  // [1:10] under bit[2:0] (0..7) -> [1:7].
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({1, 10, false, false, false}, Unsigned(3)),
      (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
  // [2:5] under signed bit[2:0] (-4..3) -> [2:3].
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, Signed(3)),
            (std::vector<int64_t>{2, 3}));
}

// LRM 19.5.7 worked example b1: bit[2:0] p1, bins b1 = {1,[2:5],[6:10]} is
// resolved to {1,[2:5],[6:7]} (the [6:10] range warns and is clamped).
TEST(ValueResolution, ExampleB1UnsignedThreeBit) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3, 4, 5}));
  EXPECT_EQ(CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff),
            (std::vector<int64_t>{6, 7}));
}

// LRM 19.5.7 worked example b2: bit[2:0] p1, bins b2 = {-1,[1:10],15} is
// resolved to {[1:7]} (the -1 and 15 singletons warn out, [1:10] clamps).
TEST(ValueResolution, ExampleB2UnsignedThreeBit) {
  CoverpointEffectiveType eff = Unsigned(3);
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3, 4, 5, 6, 7}));
}

// LRM 19.5.7 worked example b3: bit signed [2:0] p2, bins b3 = {1,[2:5],[6:10]}
// is resolved to {1,[2:3]} ([6:10] warns out, [2:5] clamps).
TEST(ValueResolution, ExampleB3SignedThreeBit) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(1, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({2, 5, false, false, false}, eff),
            (std::vector<int64_t>{2, 3}));
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({6, 10, false, false, false}, eff).empty());
}

// LRM 19.5.7 worked example b4: bit signed [2:0] p2, bins b4 = {-1,[1:10],15}
// is resolved to {-1,[1:3]} (-1 survives, 15 warns out, [1:10] clamps).
TEST(ValueResolution, ExampleB4SignedThreeBit) {
  CoverpointEffectiveType eff = Signed(3);
  EXPECT_TRUE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(-1, true, false, false, eff)));
  EXPECT_FALSE(CoverageDB::SingletonValueParticipates(
      CoverageDB::ResolveBinValue(15, false, false, false, eff)));
  EXPECT_EQ(CoverageDB::ResolveBinRange({1, 10, false, false, false}, eff),
            (std::vector<int64_t>{1, 2, 3}));
}

// LRM 19.5.7, second range bullet (wildcard exception): an x/z bit in a range
// endpoint drops the range for an ordinary bin, but for a wildcard bin the
// unknown bits are resolved to 0/1 beforehand, so the range survives and
// clamps to the effective type's domain instead of dropping out.
TEST(ValueResolution, WildcardRangeEndpointDoesNotDropRange) {
  EXPECT_TRUE(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/false},
                                  Unsigned(3))
          .empty());
  EXPECT_EQ(
      CoverageDB::ResolveBinRange({/*low=*/2, /*high=*/5, /*low_has_xz=*/false,
                                   /*high_has_xz=*/true, /*is_wildcard=*/true},
                                  Unsigned(3)),
      (std::vector<int64_t>{2, 3, 4, 5}));
}

// LRM 19.5.7, third range bullet: the values expressible by the effective type
// form the closed domain a surviving range intersects with — an unsigned type
// starts at zero, a signed type spans its two's-complement range.
TEST(ValueResolution, ExpressibleDomainBoundsByEffectiveType) {
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Unsigned(3)), 0);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Unsigned(3)), 7);
  EXPECT_EQ(CoverageDB::EffectiveTypeMin(Signed(3)), -4);
  EXPECT_EQ(CoverageDB::EffectiveTypeMax(Signed(3)), 3);
}

}  // namespace
