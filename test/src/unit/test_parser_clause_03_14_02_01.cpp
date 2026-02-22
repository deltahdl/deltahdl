#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: preprocess source and return timescale state.
struct PreprocResult3140201 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult3140201 Preprocess(const std::string &src) {
  PreprocResult3140201 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  preproc.Preprocess(fid);
  result.timescale = preproc.CurrentTimescale();
  result.global_precision = preproc.GlobalPrecision();
  result.has_timescale = preproc.HasTimescale();
  result.has_errors = diag.HasErrors();
  return result;
}

// Helper: parse source and return the compilation unit.
struct ParseResult3140201 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult3140201 Parse(const std::string &src) {
  ParseResult3140201 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM §3.14.2.1 — The `timescale compiler directive
// =============================================================================

// 32. `timescale specifies default time unit and precision for design
// elements that follow it.  §3.14.2.1: "The `timescale compiler directive
// specifies the default time unit and precision for all design elements
// that follow this directive."
TEST(ParserClause03, Cl3_14_2_1_DefaultForFollowingElements) {
  auto r = Preprocess("`timescale 10us / 100ns\n");
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
  auto r = Preprocess("`timescale 1ns / 1ps\n"
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
  auto r1 = Preprocess("`timescale 1ps / 1fs\n");
  EXPECT_TRUE(r1.has_timescale);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);
  // Second CU (separate Preprocess call): no timescale inherited.
  auto r2 = Preprocess("// no timescale here\n");
  EXPECT_FALSE(r2.has_timescale);
}

// 35. LRM example: three modules A, B, C with two `timescale directives.
// §3.14.2.1: "A second `timescale directive replaces the first directive."
// `timescale 1ns / 10ps → modules A and B
// `timescale 1ps / 1ps  → module C
TEST(ParserClause03, Cl3_14_2_1_LrmExampleThreeModules) {
  auto r = Parse("`timescale 1ns / 10ps\n"
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

// 36. File order dependency: the same module can get different timescale
// settings depending on compilation order.
// §3.14.2.1: "`timescale directive can result in file order dependency
// problems."
TEST(ParserClause03, Cl3_14_2_1_FileOrderDependency) {
  // Order 1: 1ns/10ps then module B then 1ps/1ps.
  auto r1 = Preprocess("`timescale 1ns / 10ps\n"
                       "module B; endmodule\n"
                       "`timescale 1ps / 1ps\n");
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kPs);
  // Order 2: 1ps/1ps then module B then 1ns/10ps.
  auto r2 = Preprocess("`timescale 1ps / 1ps\n"
                       "module B; endmodule\n"
                       "`timescale 1ns / 10ps\n");
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);
  // Same module B in different orders sees different timescales.
  EXPECT_NE(r1.timescale.unit, r2.timescale.unit);
}

// 37. Design elements with timeunit/timeprecision keywords are NOT
// affected by `timescale.  §3.14.2.1: "that do not have timeunit and
// timeprecision constructs specified within the design element."
TEST(ParserClause03, Cl3_14_2_1_KeywordsOverrideTimescale) {
  auto r = Parse("`timescale 1ns / 1ps\n"
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

// 38. Global precision tracks the finest precision across all `timescale
// directives.  This is necessary for delay conversion (§3.14.1).
TEST(ParserClause03, Cl3_14_2_1_GlobalPrecisionTracking) {
  // Two directives: 1ns/1ps then 1us/1ns.
  // Global precision should be the finer one: 1ps.
  auto r = Preprocess("`timescale 1ns / 1ps\n"
                      "`timescale 1us / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // Current timescale is the last one.
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
  // Global precision is the finest across all directives.
  EXPECT_EQ(r.global_precision, TimeUnit::kPs);
}

// 39. No `timescale: has_timescale is false; default timescale values.
TEST(ParserClause03, Cl3_14_2_1_NoTimescaleDefault) {
  auto r = Preprocess("// no directives\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.has_timescale);
  // Default TimeScale struct values (ns/ns).
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
}

// 40. Error: missing slash in `timescale.
TEST(ParserClause03, Cl3_14_2_1_ErrorMissingSlash) {
  auto r = Preprocess("`timescale 1ns 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 41. Error: invalid magnitude (must be 1, 10, or 100).
TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidMagnitude) {
  auto r = Preprocess("`timescale 5ns / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 42. Error: invalid time unit string.
TEST(ParserClause03, Cl3_14_2_1_ErrorInvalidUnit) {
  auto r = Preprocess("`timescale 1xx / 1ps\n");
  EXPECT_TRUE(r.has_errors);
}

// 43. Delay conversion uses `timescale values.  A delay of 1 under
// `timescale 10ns/1ns converts to 10 ticks at ns global precision.
TEST(ParserClause03, Cl3_14_2_1_DelayConversionWithTimescale) {
  auto r = Preprocess("`timescale 10ns / 1ns\n");
  EXPECT_FALSE(r.has_errors);
  // A delay of 3 in this timescale = 3 * 10ns = 30ns = 30 ticks at ns.
  EXPECT_EQ(DelayToTicks(3, r.timescale, r.global_precision), 30u);
  // Real delay 1.5 = 1.5 * 10ns = 15ns, rounded to 1ns step = 15 ticks.
  EXPECT_EQ(RealDelayToTicks(1.5, r.timescale, r.global_precision), 15u);
}

// 44. Syntax: whitespace around slash is optional.
// §3.14.2.1 examples show both "1ns / 10ps" and "1ps/1ps".
TEST(ParserClause03, Cl3_14_2_1_WhitespaceAroundSlash) {
  // No spaces around slash.
  auto r1 = Preprocess("`timescale 1ns/1ps\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r1.timescale.precision, TimeUnit::kPs);
  // Spaces around slash.
  auto r2 = Preprocess("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r2.timescale.precision, TimeUnit::kPs);
}
