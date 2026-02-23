// §3.14.2: Specifying time units and precision

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
struct PreprocResult31402 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult31402 Preprocess(const std::string &src) {
  PreprocResult31402 result;
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
struct ParseResult31402 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult31402 Parse(const std::string &src) {
  ParseResult31402 result;
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

namespace {

// 25. Way 2: timeunit and timeprecision keywords specify time unit and
TEST(ParserClause03, Cl3_14_2_KeywordsSetUnitAndPrecision) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
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
  auto *mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
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
  auto *mod = r.cu->modules[0];
  // Keywords were not used — flags are false.
  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}

}  // namespace
