#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool PulseLimitsReported(const std::string& specparam,
                         const std::string& message) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    specparam " +
          specparam +
          ";\n"
          "    (a => y) = (7, 9);\n"
          "  endspecify\n"
          "endmodule\n",
      f);
  return ReportedError(f.diag.Diagnostics(), message, 3, "30.7");
}

bool PulseLimitsAccepted(const std::string& specparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    specparam " +
          specparam +
          ";\n"
          "    (a => y) = (7, 9);\n"
          "  endspecify\n"
          "endmodule\n",
      f);
  return design != nullptr && !f.has_errors;
}

TEST(PulseLimitOrderElaboration,
     DISABLED_ErrorLimitBelowRejectLimitIsReported) {
  EXPECT_TRUE(PulseLimitsReported(
      "PATHPULSE$ = (3, 1)",
      "PATHPULSE$ error limit 1 is smaller than its reject limit 3"));
}

TEST(PulseLimitOrderElaboration,
     DISABLED_PathSpecificErrorLimitBelowRejectLimitIsReported) {
  EXPECT_TRUE(PulseLimitsReported(
      "PATHPULSE$a$y = (3, 1)",
      "PATHPULSE$ error limit 1 is smaller than its reject limit 3"));
}

TEST(PulseLimitOrderElaboration,
     DISABLED_MinTypMaxErrorLimitBelowRejectLimitIsReported) {
  EXPECT_TRUE(PulseLimitsReported(
      "PATHPULSE$ = (2:3:4, 2:1:4)",
      "PATHPULSE$ error limit 1 is smaller than its reject limit 3"));
}

TEST(PulseLimitOrderElaboration,
     DISABLED_ExpressionErrorLimitBelowRejectLimitIsReported) {
  EXPECT_TRUE(PulseLimitsReported(
      "PATHPULSE$ = (1 + 2, 4 - 3)",
      "PATHPULSE$ error limit 1 is smaller than its reject limit 3"));
}

TEST(PulseLimitOrderElaboration, ErrorLimitEqualToRejectLimitIsAccepted) {
  EXPECT_TRUE(PulseLimitsAccepted("PATHPULSE$ = (3, 3)"));
}

TEST(PulseLimitOrderElaboration, ErrorLimitAboveRejectLimitIsAccepted) {
  EXPECT_TRUE(PulseLimitsAccepted("PATHPULSE$ = (1, 5)"));
}

TEST(PulseLimitOrderElaboration, PathSpecificEqualLimitsAreAccepted) {
  EXPECT_TRUE(PulseLimitsAccepted("PATHPULSE$a$y = (3, 3)"));
}

TEST(PulseLimitOrderElaboration, RejectLimitAloneIsAccepted) {
  EXPECT_TRUE(PulseLimitsAccepted("PATHPULSE$ = (3)"));
}

}  // namespace
