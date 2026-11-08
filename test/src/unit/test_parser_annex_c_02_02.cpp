#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SampledClockingEventArgDeprecated, PlainSampledIsAccepted) {
  auto r = Parse("module m; logic a, b; assign b = $sampled(a); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SampledClockingEventArgDeprecated, ClockingEventArgIsRejected) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $sampled(a, @(posedge clk)); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$sampled does not accept a clocking event argument", 1,
      "16.9.3"));
}

TEST(SampledClockingEventArgDeprecated, BareClockingEventArgIsRejected) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $sampled(a, @clk); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$sampled does not accept a clocking event argument", 1,
      "16.9.3"));
}

TEST(SampledClockingEventArgDeprecated, ClockingEventArgStillAllowedForRose) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $rose(a, @(posedge clk)); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SampledClockingEventArgDeprecated,
     BareClockingEventArgStillAllowedForFell) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $fell(a, @clk); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
