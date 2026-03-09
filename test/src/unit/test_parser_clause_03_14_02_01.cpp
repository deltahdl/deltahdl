#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_2_TimescaleWithoutKeywords) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];

  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}

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

  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kUs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kNs);
}

TEST(ParserClause03, Cl3_14_TimeScaleTwoComponents) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 1;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);

  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

}  // namespace
