#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(RunAndGetHelper, FailsOnADiagnosticTheRunRaises) {
  EXPECT_NONFATAL_FAILURE(
      RunAndGet("module top;\n"
                "  typedef union tagged { void N; int V; int O; } u_t;\n"
                "  u_t u;\n"
                "  int y;\n"
                "  initial begin\n"
                "    u = tagged V 3;\n"
                "    y = u.O;\n"
                "  end\n"
                "endmodule\n",
                "y"),
      "the run reported: run-time error: accessing member 'O' of tagged "
      "union 'u' which currently has tag 'V'");
}

TEST(RunAndGetHelper, PassesOverAWarningTheRunRaises) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int aa[int];\n"
                      "  int y;\n"
                      "  initial y = aa[7] + 3;\n"
                      "endmodule\n",
                      "y"),
            3u);
}

TEST(RunAndGetHelper, AnswersTheValueOfACleanRun) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int y;\n"
                      "  initial y = 6 * 7;\n"
                      "endmodule\n",
                      "y"),
            42u);
}

}  // namespace
