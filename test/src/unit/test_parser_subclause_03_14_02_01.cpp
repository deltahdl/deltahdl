#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, TimescaleWithoutKeywords) {
  auto r = PreprocessAndParse(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];

  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}

TEST(DesignBuildingBlockParsing, KeywordsOverrideTimescale) {
  auto r = PreprocessAndParse(
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

}  // namespace
