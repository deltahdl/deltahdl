// §3.14.2.2: The timeunit and timeprecision keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// 28. Single module with timeunit slash — precision arg is used.
TEST(ParserClause03, Cl3_14_3_SingleModuleTimeunitSlash) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1us / 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// --- timeunit / timeprecision (LRM section 3.14) ---
TEST(ParserSection23, TimeunitDecl) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  // timeunit is consumed; no items generated (just parsed and skipped).
}

TEST(ParserSection23, TimeprecisionDecl) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, TimeunitAndTimeprecision) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 100ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

using ProgramParseTest = ProgramTestParse;

// non_port_program_item ::= timeunits_declaration
TEST(SourceText, ProgramTimeunitsDecl) {
  auto r = Parse(
      "program prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// Helper: preprocess and parse, returning CU + preprocessor state.
struct ParseResult3140203 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kNs;
};

static ParseResult3140203 ParseTimescale31402(const std::string& src) {
  ParseResult3140203 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.PreprocessTimescale(fid);
  result.preproc_timescale = preproc.CurrentTimescale();
  result.has_preproc_timescale = preproc.HasTimescale();
  result.preproc_global_precision = preproc.GlobalPrecision();
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// 25. Way 2: timeunit and timeprecision keywords specify time unit and
TEST(ParserClause03, Cl3_14_2_KeywordsSetUnitAndPrecision) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

// 28. timeunit keyword handles all six time units.
TEST(ParserClause03, Cl3_14_2_TimeunitAllSixUnits) {
  auto r_s = ParseTimescale31402("module m; timeunit 1s; endmodule\n");
  EXPECT_EQ(r_s.cu->modules[0]->time_unit, TimeUnit::kS);
  auto r_ms = ParseTimescale31402("module m; timeunit 1ms; endmodule\n");
  EXPECT_EQ(r_ms.cu->modules[0]->time_unit, TimeUnit::kMs);
  auto r_us = ParseTimescale31402("module m; timeunit 1us; endmodule\n");
  EXPECT_EQ(r_us.cu->modules[0]->time_unit, TimeUnit::kUs);
  auto r_ns = ParseTimescale31402("module m; timeunit 1ns; endmodule\n");
  EXPECT_EQ(r_ns.cu->modules[0]->time_unit, TimeUnit::kNs);
  auto r_ps = ParseTimescale31402("module m; timeunit 1ps; endmodule\n");
  EXPECT_EQ(r_ps.cu->modules[0]->time_unit, TimeUnit::kPs);
  auto r_fs = ParseTimescale31402("module m; timeunit 1fs; endmodule\n");
  EXPECT_EQ(r_fs.cu->modules[0]->time_unit, TimeUnit::kFs);
}

// =============================================================================
// LRM §3.14.2.2 — The timeunit and timeprecision keywords
// =============================================================================
// 45. timeunit keyword sets the time unit of a module to a time literal.
// §3.14.2.2: "The time unit ... can be declared by the timeunit ...
// keywords, respectively, and set to a time literal."
TEST(ParserClause03, Cl3_14_2_2_TimeunitSetsUnit) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
}

// 46. timeprecision keyword sets the time precision of a module.
// §3.14.2.2: "The time ... precision can be declared by the ...
// timeprecision keywords, respectively, and set to a time literal."
TEST(ParserClause03, Cl3_14_2_2_TimeprecisionSetsPrecision) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// 47. Combined syntax: timeunit with slash separator sets both unit and
// precision.  §3.14.2.2: "The time precision may also be declared using
// an optional second argument to the timeunit keyword using the slash
// separator."
TEST(ParserClause03, Cl3_14_2_2_TimeunitSlashSetsBoth) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kPs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kFs);
}

// 48. LRM Example D: timeunit and timeprecision as separate keywords.
// §3.14.2.2:
//   module D (...);
//     timeunit 100ps;
//     timeprecision 10fs;
TEST(ParserClause03, Cl3_14_2_2_LrmExampleD) {
  auto r = ParseTimescale31402(
      "module D;\n"
      "  timeunit 100ps;\n"
      "  timeprecision 10fs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kPs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kFs);
}

}  // namespace
