#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// RunAndGet fails the case for a diagnostic the run raises: a read of a
// tagged union member against another tag is a run-time error under §11.9,
// which the evaluator reports and then carries on from, leaving y at 0 -- a
// value the helper answered as if the simulator had computed it, so a case
// that expected 0 passed over the error and one that expected anything else
// read a wrong number with no word of why.
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

// A warning the run raises is no failure: §7.8.6 has a read of a nonexistent
// associative-array entry answer the default value and lets the simulator
// warn, so the value read is the standard's and the case answers it.
TEST(RunAndGetHelper, PassesOverAWarningTheRunRaises) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int aa[int];\n"
                      "  int y;\n"
                      "  initial y = aa[7] + 3;\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// A clean run fails nothing and answers the value, so the check above does not
// turn every case red.
TEST(RunAndGetHelper, AnswersTheValueOfACleanRun) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int y;\n"
                      "  initial y = 6 * 7;\n"
                      "endmodule\n",
                      "y"),
            42u);
}

}  // namespace
