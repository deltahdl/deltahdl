#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockingBlock, MalformedClockingItemNames14_4) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1step\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 4, "14.4"));
}

TEST(ClockingBlock, DefaultSkewWithTerminatorAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #1step;\n"
              "  endclocking\n"
              "endmodule\n"));
}

}  // namespace
