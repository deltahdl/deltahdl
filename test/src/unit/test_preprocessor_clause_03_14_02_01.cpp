#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_14_2_1_GlobalPrecisionTracking) {
  auto r = PreprocessTimescale(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);

  EXPECT_EQ(r.global_precision, TimeUnit::kPs);
}

TEST(ParserClause03, Cl3_14_2_TimescaleDirectiveSetsUnitAndPrecision) {
  auto r = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

TEST(ParserClause03, Cl3_14_2_TimescaleAllSixUnits) {
  auto r_s = PreprocessTimescale("`timescale 1s / 1s\n");
  EXPECT_EQ(r_s.timescale.unit, TimeUnit::kS);
  auto r_ms = PreprocessTimescale("`timescale 1ms / 1ms\n");
  EXPECT_EQ(r_ms.timescale.unit, TimeUnit::kMs);
  auto r_us = PreprocessTimescale("`timescale 1us / 1us\n");
  EXPECT_EQ(r_us.timescale.unit, TimeUnit::kUs);
  auto r_ns = PreprocessTimescale("`timescale 1ns / 1ns\n");
  EXPECT_EQ(r_ns.timescale.unit, TimeUnit::kNs);
  auto r_ps = PreprocessTimescale("`timescale 1ps / 1ps\n");
  EXPECT_EQ(r_ps.timescale.unit, TimeUnit::kPs);
  auto r_fs = PreprocessTimescale("`timescale 1fs / 1fs\n");
  EXPECT_EQ(r_fs.timescale.unit, TimeUnit::kFs);
}

TEST(ParserClause03, Cl3_14_2_1_DefaultForFollowingElements) {
  auto r = PreprocessTimescale("`timescale 10us / 100ns\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.has_timescale);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(r.timescale.magnitude, 10);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.prec_magnitude, 100);
}

TEST(ParserClause03, Cl3_14_2_1_PersistsUntilReplaced) {
  auto r = PreprocessTimescale(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_EQ(r.timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

TEST(ParserClause03, Cl3_14_2_1_CuScoped) {
  auto r1 = PreprocessTimescale("`timescale 1ps / 1fs\n");
  EXPECT_TRUE(r1.has_timescale);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);

  auto r2 = PreprocessTimescale("// no timescale here\n");
  EXPECT_FALSE(r2.has_timescale);
}

TEST(ParserClause03, Cl3_14_2_1_FileOrderDependency) {
  auto r1 = PreprocessTimescale(
      "`timescale 1ns / 10ps\n"
      "module B; endmodule\n"
      "`timescale 1ps / 1ps\n");
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);

  auto r2 = PreprocessTimescale(
      "`timescale 1ps / 1ps\n"
      "module B; endmodule\n"
      "`timescale 1ns / 10ps\n");
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);

  EXPECT_NE(r1.timescale.unit, r2.timescale.unit);
}

TEST(ParserClause03, Cl3_14_2_1_ErrorMissingSlash) {
  auto r = PreprocessTimescale("`timescale 1ns 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidMagnitude) {
  auto r = PreprocessTimescale("`timescale 5ns / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_14_2_1_WhitespaceAroundSlash) {
  auto r1 = PreprocessTimescale("`timescale 1ns/1ps\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r1.timescale.precision, TimeUnit::kPs);

  auto r2 = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r2.timescale.precision, TimeUnit::kPs);
}

TEST(ParserClause03, Cl3_14_2_1_LrmExampleThreeModules) {
  auto r = ParseWithPreprocessor(
      "`timescale 1ns / 10ps\n"
      "module A; endmodule\n"
      "module B; endmodule\n"
      "`timescale 1ps / 1ps\n"
      "module C; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);

  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[1]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[2]->has_timeunit);
}

}  // namespace
