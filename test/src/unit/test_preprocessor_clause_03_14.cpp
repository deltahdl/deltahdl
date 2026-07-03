#include <gtest/gtest.h>

#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockPreprocessing,
     TimescaleAcceptsMagnitudesOneTenHundred) {
  EXPECT_FALSE(PreprocessTimescale("`timescale 1ns / 1ps\n").has_errors);
  EXPECT_FALSE(PreprocessTimescale("`timescale 10ns / 10ps\n").has_errors);
  EXPECT_FALSE(PreprocessTimescale("`timescale 100ns / 100ps\n").has_errors);
}

TEST(DesignBuildingBlockPreprocessing, TimescaleRejectsOtherMagnitudes) {
  EXPECT_TRUE(PreprocessTimescale("`timescale 5ns / 1ps\n").has_errors);
  EXPECT_TRUE(PreprocessTimescale("`timescale 50ns / 1ps\n").has_errors);
  EXPECT_TRUE(PreprocessTimescale("`timescale 1ns / 200ps\n").has_errors);
}

TEST(DesignBuildingBlockPreprocessing, TimescaleRejectsUnknownSuffix) {
  EXPECT_TRUE(PreprocessTimescale("`timescale 1sec / 1ps\n").has_errors);
  EXPECT_TRUE(PreprocessTimescale("`timescale 1ns / 1xs\n").has_errors);
}

TEST(DesignBuildingBlockPreprocessing,
     TimescaleRangeSpansSecondsToFemtoseconds) {
  auto r_max = PreprocessTimescale("`timescale 100s / 100s\n");
  EXPECT_FALSE(r_max.has_errors);
  EXPECT_EQ(r_max.timescale.unit, TimeUnit::kS);
  EXPECT_EQ(r_max.timescale.magnitude, 100);

  auto r_min = PreprocessTimescale("`timescale 1fs / 1fs\n");
  EXPECT_FALSE(r_min.has_errors);
  EXPECT_EQ(r_min.timescale.unit, TimeUnit::kFs);
  EXPECT_EQ(r_min.timescale.magnitude, 1);
}

TEST(DesignBuildingBlockPreprocessing, TimescaleCarriesUnitAndPrecision) {
  auto r = PreprocessTimescale("`timescale 100ns / 10ps\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.magnitude, 100);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(r.timescale.prec_magnitude, 10);
}

TEST(DesignBuildingBlockPreprocessing, TimescalePrecisionLessPreciseThanUnit) {
  EXPECT_TRUE(PreprocessTimescale("`timescale 1ps / 1ns\n").has_errors);
}

TEST(DesignBuildingBlockPreprocessing, TimescaleMapsEachSuffixToCorrectUnit) {
  EXPECT_EQ(PreprocessTimescale("`timescale 1s / 1s\n").timescale.unit,
            TimeUnit::kS);
  EXPECT_EQ(PreprocessTimescale("`timescale 1ms / 1ms\n").timescale.unit,
            TimeUnit::kMs);
  EXPECT_EQ(PreprocessTimescale("`timescale 1us / 1us\n").timescale.unit,
            TimeUnit::kUs);
  EXPECT_EQ(PreprocessTimescale("`timescale 1ns / 1ns\n").timescale.unit,
            TimeUnit::kNs);
  EXPECT_EQ(PreprocessTimescale("`timescale 1ps / 1ps\n").timescale.unit,
            TimeUnit::kPs);
  EXPECT_EQ(PreprocessTimescale("`timescale 1fs / 1fs\n").timescale.unit,
            TimeUnit::kFs);
}

TEST(DesignBuildingBlockPreprocessing,
     TimescalePrecisionLongerByMagnitudeRejected) {
  EXPECT_TRUE(PreprocessTimescale("`timescale 1ns / 10ns\n").has_errors);
  EXPECT_TRUE(PreprocessTimescale("`timescale 10ps / 100ps\n").has_errors);
}

}  // namespace
