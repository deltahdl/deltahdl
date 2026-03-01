// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// 15. Config declarations at top level (part of CU).
TEST(ParserClause03, Cl3_12_1_ConfigAtCUScope) {
  auto r = ParseWithPreprocessor(
      "module lib_mod; endmodule\n"
      "config my_cfg;\n"
      "  design lib_mod;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "my_cfg");
}

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Cl3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

// 2. Table 3-1: ParseTimeUnitStr maps all six character strings.
TEST(ParserClause03, Cl3_14_Table3_1_AllUnitStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("s", u));
  EXPECT_EQ(u, TimeUnit::kS);
  EXPECT_TRUE(ParseTimeUnitStr("ms", u));
  EXPECT_EQ(u, TimeUnit::kMs);
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_TRUE(ParseTimeUnitStr("ns", u));
  EXPECT_EQ(u, TimeUnit::kNs);
  EXPECT_TRUE(ParseTimeUnitStr("ps", u));
  EXPECT_EQ(u, TimeUnit::kPs);
  EXPECT_TRUE(ParseTimeUnitStr("fs", u));
  EXPECT_EQ(u, TimeUnit::kFs);
}

// 3. Table 3-1: invalid unit strings are rejected.
TEST(ParserClause03, Cl3_14_Table3_1_InvalidStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u));  // case-sensitive
}

// 4. "us" represents microseconds (substitution for the mu-s symbol).
TEST(ParserClause03, Cl3_14_UsForMicroseconds) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_EQ(static_cast<int8_t>(u), -6);  // 10^-6 = microsecond
}

// 5. TimeScale struct: time values have two components (unit + precision).
TEST(ParserClause03, Cl3_14_TimeScaleTwoComponents) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 1;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);
  // Unit and precision are independently stored.
  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

// 12. Precision constraint: precision exponent <= unit exponent.
// Finer units have more-negative exponents (kFs < kPs < ... < kS).
TEST(ParserClause03, Cl3_14_PrecisionAtLeastAsPreciseAsUnit) {
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kFs),
            static_cast<int8_t>(TimeUnit::kPs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kPs),
            static_cast<int8_t>(TimeUnit::kNs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kNs),
            static_cast<int8_t>(TimeUnit::kUs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kUs),
            static_cast<int8_t>(TimeUnit::kMs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kMs),
            static_cast<int8_t>(TimeUnit::kS));
}

// ===========================================================================
// §3.14: Timeunit/timeprecision parsing
// ===========================================================================
TEST(Lexical, Timeunit_BasicParse) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  // Should parse without error. The timeunit decl is consumed.
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Lexical, Timeprecision_BasicParse) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_WithSlash) {
  // timeunit 1ns / 1ps;  (combined form)
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_DifferentValues) {
  // Various time unit values
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 100us;\n"
      "  timeprecision 10ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

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
