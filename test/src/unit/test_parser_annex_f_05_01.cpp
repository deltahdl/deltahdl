#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InClockingEvent(const std::string& name) {
  return "local variable \"" + name +
         "\" may not be used in a clocking event expression";
}

TEST(ClockRewritePrecondition, APropertyBodyLocalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    logic v;\n"
      "    @(posedge v) (a, v = b) |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalInANestedClockGuardIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk) (a, v = b) |-> @(posedge clk iff v) c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalInAParenthesizedGuardIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk iff (v == 1)) (a, v = b) |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, AnUnclosedEventGroupIsReadToTheEndOfTheFile) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge v");
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalFormalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic v);\n"
      "    @(posedge v) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 3, "16.10"));
}

TEST(ClockRewritePrecondition, ASequenceLocalFormalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic v);\n"
      "    @(posedge v) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 3, "16.10"));
}

TEST(ClockRewritePrecondition, AFormalThatIsNotLocalMayClockTheProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic v);\n"
      "    @(posedge v) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockRewritePrecondition, APropertyLocalOutsideTheClockIsNotReported) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input int w);\n"
      "    int v;\n"
      "    @(posedge clk) (a, v = w) |-> ##1 (b == v);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
