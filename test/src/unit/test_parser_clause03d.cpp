#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: lex a single token from source text.
// Returns both the SourceManager (owning the source buffer) and the token
// so that token.text (a string_view) remains valid.
struct LexResult {
  SourceManager mgr;
  Token token;
};

static LexResult LexOne(const std::string& src) {
  LexResult result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  result.token = lexer.Next();
  return result;
}

// Helper: parse source and return the compilation unit.
struct ParseResult3d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3d Parse(const std::string& src) {
  ParseResult3d result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM §3.14 — Simulation time units and precision
// =============================================================================

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Sec3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

// 2. Table 3-1: ParseTimeUnitStr maps all six character strings.
TEST(ParserClause03, Sec3_14_Table3_1_AllUnitStrings) {
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
TEST(ParserClause03, Sec3_14_Table3_1_InvalidStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u));  // case-sensitive
}

// 4. NOTE: "us" represents microseconds (the LRM substitutes for μs).
TEST(ParserClause03, Sec3_14_UsForMicroseconds) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_EQ(static_cast<int8_t>(u), -6);  // 10^-6 = microsecond
}

// 5. TimeScale struct: time values have two components (unit + precision).
TEST(ParserClause03, Sec3_14_TimeScaleTwoComponents) {
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

// 6. Three orders of magnitude: 1, 10, 100.
// DelayToTicks produces proportionally different tick counts.
TEST(ParserClause03, Sec3_14_ThreeMagnitudes) {
  TimeScale ts1{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  TimeScale ts10{TimeUnit::kNs, 10, TimeUnit::kPs, 1};
  TimeScale ts100{TimeUnit::kNs, 100, TimeUnit::kPs, 1};
  EXPECT_EQ(DelayToTicks(1, ts1, TimeUnit::kPs), 1000u);
  EXPECT_EQ(DelayToTicks(1, ts10, TimeUnit::kPs), 10000u);
  EXPECT_EQ(DelayToTicks(1, ts100, TimeUnit::kPs), 100000u);
}

// 7. Lexer: all six time suffixes produce kTimeLiteral tokens.
TEST(ParserClause03, Sec3_14_LexerAllTimeSuffixes) {
  auto r_s = LexOne("1s");
  EXPECT_EQ(r_s.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_s.token.text, "1s");
  auto r_ms = LexOne("1ms");
  EXPECT_EQ(r_ms.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ms.token.text, "1ms");
  auto r_us = LexOne("1us");
  EXPECT_EQ(r_us.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_us.token.text, "1us");
  auto r_ns = LexOne("1ns");
  EXPECT_EQ(r_ns.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ns.token.text, "1ns");
  auto r_ps = LexOne("1ps");
  EXPECT_EQ(r_ps.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ps.token.text, "1ps");
  auto r_fs = LexOne("1fs");
  EXPECT_EQ(r_fs.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_fs.token.text, "1fs");
}

// 8. Lexer: magnitudes 1, 10, 100 with time suffix.
TEST(ParserClause03, Sec3_14_LexerTimeMagnitudes) {
  auto r1 = LexOne("1ns");
  EXPECT_EQ(r1.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r1.token.text, "1ns");
  auto r10 = LexOne("10ns");
  EXPECT_EQ(r10.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r10.token.text, "10ns");
  auto r100 = LexOne("100ns");
  EXPECT_EQ(r100.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r100.token.text, "100ns");
}

// 9. SimTime: simulation time is maintained as ticks with comparison
// and addition operators.
TEST(ParserClause03, Sec3_14_SimTimeOperations) {
  SimTime t0{0};
  SimTime t1{1000};
  SimTime t2{1000};
  EXPECT_EQ(t0.ticks, 0u);
  EXPECT_EQ(t1.ticks, 1000u);
  EXPECT_TRUE(t0 < t1);
  EXPECT_TRUE(t0 <= t1);
  EXPECT_FALSE(t0 > t1);
  EXPECT_TRUE(t1 > t0);
  EXPECT_TRUE(t1 == t2);
  SimTime t3 = t0 + t1;
  EXPECT_EQ(t3.ticks, 1000u);
}

// 10. DelayToTicks: when unit == precision, delay maps 1:1 to ticks.
TEST(ParserClause03, Sec3_14_DelayToTicksSameUnit) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  EXPECT_EQ(DelayToTicks(42, ts, TimeUnit::kNs), 42u);
}

// 11. DelayToTicks covers the full range from seconds to femtoseconds.
TEST(ParserClause03, Sec3_14_DelayToTicksFullRange) {
  // 1 second at fs precision = 10^15 ticks.
  TimeScale ts_s{TimeUnit::kS, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_s, TimeUnit::kFs), 1000000000000000ULL);
  // 1 fs at fs precision = 1 tick.
  TimeScale ts_fs{TimeUnit::kFs, 1, TimeUnit::kFs, 1};
  EXPECT_EQ(DelayToTicks(1, ts_fs, TimeUnit::kFs), 1u);
}

// 12. Precision constraint: precision exponent <= unit exponent.
// "The time precision shall be at least as precise as the time unit."
// Finer units have more-negative exponents (kFs < kPs < ... < kS).
TEST(ParserClause03, Sec3_14_PrecisionAtLeastAsPreciseAsUnit) {
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

// 13. Time values stored in design element: module with timeunit and
// timeprecision stores both components.
TEST(ParserClause03, Sec3_14_TimeValuesInDesignElement) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// =============================================================================
// LRM §3.14.1 — Time value rounding
// =============================================================================

// 14. Same precision as unit: delay values rounded to whole numbers.
// "If the precision is the same as the time units, then delay values are
// rounded off to whole numbers (integers)."
TEST(ParserClause03, Sec3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  // 2.75ns with 1ns precision rounds to 3ns = 3 ticks at ns.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  // 2.3ns rounds to 2ns.
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  // 2.5ns rounds to 3ns (round half away from zero).
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// 15. One order of magnitude smaller: rounds to one decimal place.
// "If the precision is one order of magnitude smaller than the time units,
// then delay values are rounded off to one decimal place."
TEST(ParserClause03, Sec3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  // 1ns unit, 100ps precision → 1 decimal place in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns → 2.8ns = 2800ps = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // 2.73ns → 2.7ns = 2700ps.
  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

// 16. LRM example: "if the time unit specified is 1ns and the precision
// is 100ps, then ... a delay of 2.75ns would be rounded off to 2.8ns."
TEST(ParserClause03, Sec3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns rounded to nearest 100ps = 2.8ns = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // Verify in ns-tick form: at ns precision, 2800ps = 2.8ns ≈ 3 ticks.
  // But at ps global precision the value is 2800.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

// 17. Two orders of magnitude smaller: rounds to two decimal places.
TEST(ParserClause03, Sec3_14_1_TwoOrdersSmaller) {
  // 1ns unit, 10ps precision → 2 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};
  // 2.756ns → 2.76ns = 2760ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);
  // 2.754ns → 2.75ns = 2750ps.
  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

// 18. Three orders (full precision): no rounding needed.
TEST(ParserClause03, Sec3_14_1_ThreeOrdersNoRounding) {
  // 1ns unit, 1ps precision → 3 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // 2.756ns = 2756ps exactly, no rounding.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

// 19. Zero delay: rounds to zero regardless of precision.
TEST(ParserClause03, Sec3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Sec3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

// 21. Per-element accuracy: "The time values in a design element are
// accurate to within the unit of time precision specified for that
// design element, even if there is a smaller time precision specified
// elsewhere in the design."
TEST(ParserClause03, Sec3_14_1_PerElementAccuracy) {
  // Element A: 1ns / 100ps — rounds to 0.1ns steps.
  TimeScale ts_a{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // Element B: 1ns / 1ps — rounds to 0.001ns steps.
  TimeScale ts_b{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // Same delay 2.756ns produces different results per element.
  // Element A: 2.756 → 2.8ns = 2800ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs), 2800u);
  // Element B: 2.756 → 2.756ns = 2756ps (no rounding at 1ps).
  EXPECT_EQ(RealDelayToTicks(2.756, ts_b, TimeUnit::kPs), 2756u);
  // The two results differ because each element uses its own precision.
  EXPECT_NE(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs),
            RealDelayToTicks(2.756, ts_b, TimeUnit::kPs));
}

// 22. Magnitude affects rounding: 10ns unit with 1ns precision.
TEST(ParserClause03, Sec3_14_1_MagnitudeRounding) {
  // 10ns unit, 1ns precision → delays in multiples of 10ns, rounded to 1ns.
  TimeScale ts{TimeUnit::kNs, 10, TimeUnit::kNs, 1};
  // delay=2.75 means 2.75 * 10ns = 27.5ns → rounds to 28ns = 28 ticks.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 28u);
  // delay=1.0 means 10ns = 10 ticks.
  EXPECT_EQ(RealDelayToTicks(1.0, ts, TimeUnit::kNs), 10u);
}

// 23. Rounding with global precision finer than element precision.
// Global precision = fs, element precision = 100ps.
// Rounding still occurs at element's precision step.
TEST(ParserClause03, Sec3_14_1_FinerGlobalPrecision) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns at fs global precision:
  // raw ticks = 2.75 * 10^6 = 2750000 fs.
  // precision step = 100 * 10^3 = 100000 fs.
  // 2750000 / 100000 = 27.5 → round to 28 → 28 * 100000 = 2800000 fs.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kFs), 2800000u);
}
