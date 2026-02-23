// §3.14.2.1: The `timescale compiler directive

#include <gtest/gtest.h>
#include "common/types.h"

using namespace delta;

namespace {

// 37. Design elements with timeunit/timeprecision keywords are NOT
// affected by `timescale.  §3.14.2.1: "that do not have timeunit and
// timeprecision constructs specified within the design element."
TEST(ParserClause03, Cl3_14_2_1_KeywordsOverrideTimescale) {
  auto r = Parse(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  // Module has explicit keywords — they take priority over `timescale.
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kUs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kNs);
}

}  // namespace
