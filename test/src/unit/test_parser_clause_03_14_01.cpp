#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_1_PerElementAccuracy) {
  TimeScale ts_a{TimeUnit::kNs, 1, TimeUnit::kPs, 100};

  TimeScale ts_b{TimeUnit::kNs, 1, TimeUnit::kPs, 1};

  EXPECT_EQ(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs), 2800u);

  EXPECT_EQ(RealDelayToTicks(2.756, ts_b, TimeUnit::kPs), 2756u);

  EXPECT_NE(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs),
            RealDelayToTicks(2.756, ts_b, TimeUnit::kPs));
}

TEST(ParserClause03, Cl3_14_1_MagnitudeRounding) {
  TimeScale ts{TimeUnit::kNs, 10, TimeUnit::kNs, 1};

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 28u);

  EXPECT_EQ(RealDelayToTicks(1.0, ts, TimeUnit::kNs), 10u);
}

TEST(ParserClause03, Cl3_14_1_FinerGlobalPrecision) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kFs), 2800000u);
}

TEST(ParserClause03, Cl3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);

  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);

  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

TEST(ParserClause03, Cl3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);

  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

TEST(ParserClause03, Cl3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);

  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

TEST(ParserClause03, Cl3_14_1_TwoOrdersSmaller) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};

  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);

  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

TEST(ParserClause03, Cl3_14_1_ThreeOrdersNoRounding) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};

  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

TEST(ParserClause03, Cl3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};

  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);

  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
