#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"
#include "parser/time_resolve.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, TimescaleWithoutKeywords) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

TEST(DesignBuildingBlockParsing, TimescaleSuppliesDefaultsToFollowingModule) {
  auto r = ParseTimescale31402(
      "`timescale 10ns / 1ns\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

// §3.14.2.1 C1: the directive supplies the default only for the component the
// element itself does not declare. Here the module declares its own time unit
// (via §3.14.2.2 `timeunit`) but no precision, so the module's unit wins while
// the directive fills in the missing precision.
TEST(DesignBuildingBlockParsing,
     TimescaleSuppliesPrecisionWhenElementDeclaresOnlyUnit) {
  auto r = ParseTimescale31402(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "  timeunit 1us;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  // Unit comes from the module's own keyword (kUs), not the directive (kNs).
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  // Precision is supplied by the directive because the module omitted it.
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kPs);
}

// §3.14.2.1 C1, mirror form: the module declares its own precision (via
// §3.14.2.2 `timeprecision`) but no unit, so the directive supplies the unit
// while the module's precision wins.
TEST(DesignBuildingBlockParsing,
     TimescaleSuppliesUnitWhenElementDeclaresOnlyPrecision) {
  auto r = ParseTimescale31402(
      "`timescale 10us / 100ns\n"
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  // Unit is supplied by the directive because the module omitted it.
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  // Precision comes from the module's own keyword (kPs), not the directive
  // (kNs).
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kPs);
}

}  // namespace
