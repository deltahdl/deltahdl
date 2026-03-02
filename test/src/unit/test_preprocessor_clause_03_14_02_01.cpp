// §3.14.2.1: The `timescale compiler directive

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

// 38. Global precision tracks the finest precision across all `timescale
// directives.  This is necessary for delay conversion (§3.14.1).
TEST(ParserClause03, Cl3_14_2_1_GlobalPrecisionTracking) {
  // Two directives: 1ns/1ps then 1us/1ns.
  // Global precision should be the finer one: 1ps.
  auto r = PreprocessTimescale(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // Current timescale is the last one.
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  // Global precision is the finest across all directives.
  EXPECT_EQ(r.global_precision, TimeUnit::kPs);
}

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.PreprocessTimescale(fid);
}

// =============================================================================
// LRM §3.14.2 — Specifying time units and precision
// =============================================================================
// 24. Way 1: `timescale compiler directive specifies both time unit and
TEST(ParserClause03, Cl3_14_2_TimescaleDirectiveSetsUnitAndPrecision) {
  auto r = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

// 27. `timescale handles all six time units from Table 3-1.
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

// =============================================================================
// LRM §3.14.2.1 — The `timescale compiler directive
// =============================================================================
// 32. `timescale specifies default time unit and precision for design
// elements that follow it.  §3.14.2.1: "The `timescale compiler directive
// specifies the default time unit and precision for all design elements
// that follow this directive."
TEST(ParserClause03, Cl3_14_2_1_DefaultForFollowingElements) {
  auto r = PreprocessTimescale("`timescale 10us / 100ns\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.has_timescale);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(r.timescale.magnitude, 10);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.prec_magnitude, 100);
}

// 33. `timescale remains in effect until another `timescale is read.
// §3.14.2.1: "The `timescale directive remains in effect from when it is
// encountered in the source code until another `timescale compiler
// directive is read."
TEST(ParserClause03, Cl3_14_2_1_PersistsUntilReplaced) {
  // Two directives: second replaces first.
  auto r = PreprocessTimescale(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // Final state reflects the second directive.
  EXPECT_EQ(r.timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

// 34. `timescale only affects the current compilation unit.
// §3.14.2.1: "The `timescale directive only affects the current
// compilation unit; it does not span multiple compilation units."
TEST(ParserClause03, Cl3_14_2_1_CuScoped) {
  // First CU: set timescale.
  auto r1 = PreprocessTimescale("`timescale 1ps / 1fs\n");
  EXPECT_TRUE(r1.has_timescale);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);
  // Second CU (separate Preprocess call): no timescale inherited.
  auto r2 = PreprocessTimescale("// no timescale here\n");
  EXPECT_FALSE(r2.has_timescale);
}

// 36. File order dependency: the same module can get different timescale
// settings depending on compilation order.
// §3.14.2.1: "`timescale directive can result in file order dependency
// problems."
TEST(ParserClause03, Cl3_14_2_1_FileOrderDependency) {
  // Order 1: 1ns/10ps then module B then 1ps/1ps.
  auto r1 = PreprocessTimescale(
      "`timescale 1ns / 10ps\n"
      "module B; endmodule\n"
      "`timescale 1ps / 1ps\n");
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);
  // Order 2: 1ps/1ps then module B then 1ns/10ps.
  auto r2 = PreprocessTimescale(
      "`timescale 1ps / 1ps\n"
      "module B; endmodule\n"
      "`timescale 1ns / 10ps\n");
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);
  // Same module B in different orders sees different timescales.
  EXPECT_NE(r1.timescale.unit, r2.timescale.unit);
}

// 40. Error: missing slash in `timescale.
TEST(ParserClause03, Cl3_14_2_1_ErrorMissingSlash) {
  auto r = PreprocessTimescale("`timescale 1ns 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 41. Error: invalid magnitude (must be 1, 10, or 100).
TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidMagnitude) {
  auto r = PreprocessTimescale("`timescale 5ns / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 44. Syntax: whitespace around slash is optional.
// §3.14.2.1 examples show both "1ns / 10ps" and "1ps/1ps".
TEST(ParserClause03, Cl3_14_2_1_WhitespaceAroundSlash) {
  // No spaces around slash.
  auto r1 = PreprocessTimescale("`timescale 1ns/1ps\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r1.timescale.precision, TimeUnit::kPs);
  // Spaces around slash.
  auto r2 = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r2.timescale.precision, TimeUnit::kPs);
}

// 35. LRM example: three modules A, B, C with two `timescale directives.
// §3.14.2.1:
// `timescale 1ns / 10ps → modules A and B
// `timescale 1ps / 1ps  → module C
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
  // All three modules parse; none have explicit timeunit keywords.
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[1]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[2]->has_timeunit);
}

}  // namespace
