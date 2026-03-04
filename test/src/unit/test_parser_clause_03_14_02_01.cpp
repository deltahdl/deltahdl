// §3.14.2.1: The `timescale compiler directive

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 31. Module with `timescale but no explicit timeunit/timeprecision:
// has_timeunit=false (keywords were not used), but the preprocessor
// carries the timescale state for this module.
TEST(ParserClause03, Cl3_14_2_TimescaleWithoutKeywords) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  // Keywords were not used — flags are false.
  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}

// 37. Design elements with timeunit/timeprecision keywords are NOT
// affected by `timescale.  §3.14.2.1: "that do not have timeunit and
// timeprecision constructs specified within the design element."
TEST(ParserClause03, Cl3_14_2_1_KeywordsOverrideTimescale) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  // Module has explicit keywords — they take priority over `timescale.
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kUs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kNs);
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

}  // namespace
