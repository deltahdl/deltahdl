// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(Lexical, Timeunit_StoredInModuleDecl_Values) {
  // The timeunit/timeprecision values should be stored in ModuleDecl.
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Flags) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
}

// =============================================================================
// LRM §3.14.1 — Time value rounding
// =============================================================================
// 14. Same precision as unit: delay values rounded to whole numbers.
TEST(ParserClause03, Cl3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  // 2.75ns with 1ns precision rounds to 3ns = 3 ticks at ns.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  // 2.3ns rounds to 2ns.
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  // 2.5ns rounds to 3ns (round half away from zero).
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// 15. One order of magnitude smaller: rounds to one decimal place.
TEST(ParserClause03, Cl3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  // 1ns unit, 100ps precision → 1 decimal place in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns → 2.8ns = 2800ps = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // 2.73ns → 2.7ns = 2700ps.
  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

// 16. Rounding example: 1ns unit, 100ps precision, 2.75ns rounds to 2.8ns.
TEST(ParserClause03, Cl3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns rounded to nearest 100ps = 2.8ns = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // Verify in ns-tick form: at ns precision, 2800ps = 2.8ns ≈ 3 ticks.
  // But at ps global precision the value is 2800.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

// 17. Two orders of magnitude smaller: rounds to two decimal places.
TEST(ParserClause03, Cl3_14_1_TwoOrdersSmaller) {
  // 1ns unit, 10ps precision → 2 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};
  // 2.756ns → 2.76ns = 2760ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);
  // 2.754ns → 2.75ns = 2750ps.
  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

// 18. Three orders (full precision): no rounding needed.
TEST(ParserClause03, Cl3_14_1_ThreeOrdersNoRounding) {
  // 1ns unit, 1ps precision → 3 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // 2.756ns = 2756ps exactly, no rounding.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

// 19. Zero delay: rounds to zero regardless of precision.
TEST(ParserClause03, Cl3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
