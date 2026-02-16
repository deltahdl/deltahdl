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
struct PreprocResult3_14_02 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult3_14_02 Preprocess(const std::string& src) {
  PreprocResult3_14_02 result;
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
struct ParseResult3_14_02 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_14_02 Parse(const std::string& src) {
  ParseResult3_14_02 result;
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
// LRM §3.14.2 — Specifying time units and precision
// =============================================================================

// 24. Way 1: `timescale compiler directive specifies both time unit and
// precision.  "Using the compiler directive `timescale"
TEST(ParserClause03, Cl3_14_2_TimescaleDirectiveSetsUnitAndPrecision) {
  auto r = Preprocess("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.magnitude, 1);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(r.timescale.prec_magnitude, 1);
}

// 25. Way 2: timeunit and timeprecision keywords specify time unit and
// precision independently.  "Using the keywords timeunit and timeprecision"
TEST(ParserClause03, Cl3_14_2_KeywordsSetUnitAndPrecision) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// 26. Way 2 alternate: timeunit with slash separator combines both.
TEST(ParserClause03, Cl3_14_2_TimeunitSlashCombinesBoth) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// 27. `timescale handles all six time units from Table 3-1.
TEST(ParserClause03, Cl3_14_2_TimescaleAllSixUnits) {
  auto r_s = Preprocess("`timescale 1s / 1s\n");
  EXPECT_EQ(r_s.timescale.unit, TimeUnit::kS);
  auto r_ms = Preprocess("`timescale 1ms / 1ms\n");
  EXPECT_EQ(r_ms.timescale.unit, TimeUnit::kMs);
  auto r_us = Preprocess("`timescale 1us / 1us\n");
  EXPECT_EQ(r_us.timescale.unit, TimeUnit::kUs);
  auto r_ns = Preprocess("`timescale 1ns / 1ns\n");
  EXPECT_EQ(r_ns.timescale.unit, TimeUnit::kNs);
  auto r_ps = Preprocess("`timescale 1ps / 1ps\n");
  EXPECT_EQ(r_ps.timescale.unit, TimeUnit::kPs);
  auto r_fs = Preprocess("`timescale 1fs / 1fs\n");
  EXPECT_EQ(r_fs.timescale.unit, TimeUnit::kFs);
}

// 28. timeunit keyword handles all six time units.
TEST(ParserClause03, Cl3_14_2_TimeunitAllSixUnits) {
  auto r_s = Parse("module m; timeunit 1s; endmodule\n");
  EXPECT_EQ(r_s.cu->modules[0]->time_unit, TimeUnit::kS);
  auto r_ms = Parse("module m; timeunit 1ms; endmodule\n");
  EXPECT_EQ(r_ms.cu->modules[0]->time_unit, TimeUnit::kMs);
  auto r_us = Parse("module m; timeunit 1us; endmodule\n");
  EXPECT_EQ(r_us.cu->modules[0]->time_unit, TimeUnit::kUs);
  auto r_ns = Parse("module m; timeunit 1ns; endmodule\n");
  EXPECT_EQ(r_ns.cu->modules[0]->time_unit, TimeUnit::kNs);
  auto r_ps = Parse("module m; timeunit 1ps; endmodule\n");
  EXPECT_EQ(r_ps.cu->modules[0]->time_unit, TimeUnit::kPs);
  auto r_fs = Parse("module m; timeunit 1fs; endmodule\n");
  EXPECT_EQ(r_fs.cu->modules[0]->time_unit, TimeUnit::kFs);
}

// 29. Both mechanisms handle all three magnitudes (1, 10, 100).
TEST(ParserClause03, Cl3_14_2_BothMechanismsMagnitudes) {
  // `timescale with magnitudes.
  auto r1 = Preprocess("`timescale 1ns / 1ps\n");
  EXPECT_EQ(r1.timescale.magnitude, 1);
  auto r10 = Preprocess("`timescale 10ns / 10ps\n");
  EXPECT_EQ(r10.timescale.magnitude, 10);
  auto r100 = Preprocess("`timescale 100ns / 100ps\n");
  EXPECT_EQ(r100.timescale.magnitude, 100);
  // timeunit with magnitudes: all three parse successfully.
  EXPECT_FALSE(Parse("module m; timeunit 1ns; endmodule\n").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 10ns; endmodule\n").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 100ns; endmodule\n").has_errors);
}

// 30. Equivalent specifications: both mechanisms specify the same time values.
// `timescale 1ns/1ps is equivalent to timeunit 1ns; timeprecision 1ps.
TEST(ParserClause03, Cl3_14_2_EquivalentSpecifications) {
  // Way 1: `timescale directive.
  auto pp = Preprocess("`timescale 1ns / 1ps\n");
  EXPECT_FALSE(pp.has_errors);
  // Way 2: keywords inside a module.
  auto pr = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(pr.has_errors);
  // Both specify the same unit and precision.
  EXPECT_EQ(pp.timescale.unit, pr.cu->modules[0]->time_unit);
  EXPECT_EQ(pp.timescale.precision, pr.cu->modules[0]->time_prec);
}

// 31. Module with `timescale but no explicit timeunit/timeprecision:
// has_timeunit=false (keywords were not used), but the preprocessor
// carries the timescale state for this module.
TEST(ParserClause03, Cl3_14_2_TimescaleWithoutKeywords) {
  auto r = Parse(
      "`timescale 1ns / 1ps\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  // Keywords were not used — flags are false.
  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}
