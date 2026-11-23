#include <gtest/gtest.h>

#include <cstdint>

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

constexpr const char* kSampledEventReport =
    "$sampled does not accept a clocking event argument";

void ExpectSampledEventReported(const char* src) {
  auto r = Parse(src);
  const uint32_t kLine = LineHolding(src, "$sampled");
  EXPECT_TRUE(ReportedError(r.diags, kSampledEventReport, kLine, "16.9.3"))
      << src;
}

TEST(SampledClockingEventArgDeprecated,
     ClockingEventArgIsRejectedOutsideAssertions) {
  const char* const kSources[] = {
      "module m;\n  logic a, b, clk;\n"
      "  always_comb b = $sampled(a, @(posedge clk));\nendmodule\n",
      "module m;\n  logic a, clk;\n"
      "  function automatic logic f();\n"
      "    return $sampled(a, @(posedge clk));\n  endfunction\nendmodule\n",
      "interface ifc;\n  logic a, b, clk;\n"
      "  assign b = $sampled(a, @(posedge clk));\nendinterface\n",
      "program p;\n  logic a, b, clk;\n"
      "  initial b = $sampled(a, @(posedge clk));\nendprogram\n",
      "checker chk(input logic a, input logic clk);\n"
      "  logic b;\n"
      "  always_ff @(posedge clk) b <= $sampled(a, @(posedge clk));\n"
      "endchecker\n",
  };
  for (const char* src : kSources) ExpectSampledEventReported(src);
}

TEST(SampledClockingEventArgDeprecated,
     DISABLED_ClockingEventArgIsRejectedInAnAssertionAndASequence) {
  const char* const kSources[] = {
      "module m;\n  logic a, clk;\n"
      "  assert property (@(posedge clk) $sampled(a, @(posedge clk)));\n"
      "endmodule\n",
      "module m;\n  logic a, clk;\n"
      "  sequence s;\n    @(posedge clk) $sampled(a, @(posedge clk));\n"
      "  endsequence\nendmodule\n",
  };
  for (const char* src : kSources) ExpectSampledEventReported(src);
}

TEST(SampledClockingEventArgDeprecated, PlainSampledIsAcceptedEverywhere) {
  const char* const kSources[] = {
      "module m;\n  logic a, b, clk;\n"
      "  always_comb b = $sampled(a);\nendmodule\n",
      "module m;\n  logic a, clk;\n"
      "  assert property (@(posedge clk) $sampled(a));\nendmodule\n",
      "module m;\n  logic a, clk;\n"
      "  sequence s;\n    @(posedge clk) $sampled(a);\n"
      "  endsequence\nendmodule\n",
      "module m;\n  logic a, clk;\n"
      "  function automatic logic f();\n"
      "    return $sampled(a);\n  endfunction\nendmodule\n",
      "interface ifc;\n  logic a, b, clk;\n"
      "  assign b = $sampled(a);\nendinterface\n",
      "program p;\n  logic a, b, clk;\n"
      "  initial b = $sampled(a);\nendprogram\n",
      "checker chk(input logic a, input logic clk);\n"
      "  logic b;\n"
      "  always_ff @(posedge clk) b <= $sampled(a);\n"
      "endchecker\n",
  };
  for (const char* src : kSources) {
    auto r = Parse(src);
    EXPECT_FALSE(r.has_errors) << src;
  }
}

}  // namespace
