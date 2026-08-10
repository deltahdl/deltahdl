// §14.4 states the input and output skews of a clocking block, including the
// `default input/output skew` form that sets them for the whole block. The
// parser reads that form in ParseClockingDefaultSkews, and until this file
// existed no parser test reached it: the tier had
// test_elaborator_subclause_14_04 and test_simulator_subclause_14_04 and no
// parser counterpart at all.

#include "fixture_parser.h"

using namespace delta;

namespace {

// §14.4 gives the default skew declaration a terminating ';'. A block-wide skew
// written without one is rejected, and the report names §14.4 rather than the
// token it was looking for, so a reader is told which rule the source broke.
TEST(ClockingBlock, MalformedClockingItemNames14_4) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1step\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_FALSE(r.diags.empty());
  EXPECT_EQ(r.diags.front().subclause, "14.4");
  EXPECT_EQ(r.diags.front().loc.line, 4u);
  EXPECT_EQ(r.diags.front().loc.column, 3u);
}

// The same declaration written with its ';' is accepted, so the case above
// fails on the missing terminator and not on the skew before it.
TEST(ClockingBlock, DefaultSkewWithTerminatorAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #1step;\n"
              "  endclocking\n"
              "endmodule\n"));
}

}  // namespace
