// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// 21. Per-element accuracy: each design element rounds to its own precision,
// independent of finer precision specified elsewhere in the design.
TEST(ParserClause03, Cl3_14_1_PerElementAccuracy) {
  // Element A: 1ns / 100ps — rounds to 0.1ns steps.
  TimeScale ts_a{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // Element B: 1ns / 1ps — rounds to 0.001ns steps.
  TimeScale ts_b{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // Same delay 2.756ns produces different results per element.
  // Element A: 2.756 → 2.8ns = 2800ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs), 2800u);
  // Element B: 2.756 → 2.756ns = 2756ps (no rounding at 1ps).
  EXPECT_EQ(RealDelayToTicks(2.756, ts_b, TimeUnit::kPs), 2756u);
  // The two results differ because each element uses its own precision.
  EXPECT_NE(RealDelayToTicks(2.756, ts_a, TimeUnit::kPs),
            RealDelayToTicks(2.756, ts_b, TimeUnit::kPs));
}

// 22. Magnitude affects rounding: 10ns unit with 1ns precision.
TEST(ParserClause03, Cl3_14_1_MagnitudeRounding) {
  // 10ns unit, 1ns precision → delays in multiples of 10ns, rounded to 1ns.
  TimeScale ts{TimeUnit::kNs, 10, TimeUnit::kNs, 1};
  // delay=2.75 means 2.75 * 10ns = 27.5ns → rounds to 28ns = 28 ticks.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 28u);
  // delay=1.0 means 10ns = 10 ticks.
  EXPECT_EQ(RealDelayToTicks(1.0, ts, TimeUnit::kNs), 10u);
}

// 23. Rounding with global precision finer than element precision.
// Global precision = fs, element precision = 100ps.
// Rounding still occurs at element's precision step.
TEST(ParserClause03, Cl3_14_1_FinerGlobalPrecision) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns at fs global precision:
  // raw ticks = 2.75 * 10^6 = 2750000 fs.
  // precision step = 100 * 10^3 = 100000 fs.
  // 2750000 / 100000 = 27.5 → round to 28 → 28 * 100000 = 2800000 fs.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kFs), 2800000u);
}

// Helper: preprocess source and return timescale state.
struct PreprocResult31402 {
  SourceManager mgr;
  TimeScale timescale;
  TimeUnit global_precision;
  bool has_timescale;
  bool has_errors;
};

static PreprocResult31402 Preprocess(const std::string& src) {
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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31402 Parse(const std::string& src) {
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

// 25. Way 2: timeunit and timeprecision keywords specify time unit and
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
  auto* mod = r.cu->modules[0];
  // Keywords were not used — flags are false.
  EXPECT_FALSE(mod->has_timeunit);
  EXPECT_FALSE(mod->has_timeprecision);
}

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
  auto* mod = r.cu->modules[0];
  // Module has explicit keywords — they take priority over `timescale.
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kUs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kNs);
}

// Helper: parse source and return the compilation unit.
struct ParseResult3140202 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3140202 Parse(const std::string& src) {
  ParseResult3140202 result;
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
// LRM §3.14.2.2 — The timeunit and timeprecision keywords
// =============================================================================
// 45. timeunit keyword sets the time unit of a module to a time literal.
// §3.14.2.2: "The time unit ... can be declared by the timeunit ...
// keywords, respectively, and set to a time literal."
TEST(ParserClause03, Cl3_14_2_2_TimeunitSetsUnit) {
  auto r = Parse(
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
  auto r = Parse(
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
  auto r = Parse(
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
  auto r = Parse(
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

// 49. LRM Example E: timeunit with optional second argument.
// §3.14.2.2:
//   module E (...);
//     timeunit 100ps / 10fs;
TEST(ParserClause03, Cl3_14_2_2_LrmExampleE) {
  auto r = Parse(
      "module E;\n"
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

// 50. Keywords remove file order dependency: the same module always has
// the same time unit regardless of compilation order.
// §3.14.2.2: "Defining the timeunit and timeprecision constructs within
// the design element removes the file order dependency problems with
// compiler directives."
TEST(ParserClause03, Cl3_14_2_2_RemovesFileOrderDependency) {
  // With different preceding timescales, keywords always win.
  auto r1 = Parse(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  auto r2 = Parse(
      "`timescale 1ms / 1us\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  EXPECT_EQ(r1.cu->modules[0]->time_unit, r2.cu->modules[0]->time_unit);
  EXPECT_EQ(r1.cu->modules[0]->time_prec, r2.cu->modules[0]->time_prec);
  EXPECT_EQ(r1.cu->modules[0]->time_unit, TimeUnit::kPs);
  EXPECT_EQ(r1.cu->modules[0]->time_prec, TimeUnit::kFs);
}

// 51. At most one timeunit and one timeprecision per design element
// defines a "time scope".
// §3.14.2.2: "There shall be at most one time unit and one time
// precision for any module, program, package, or interface definition."
TEST(ParserClause03, Cl3_14_2_2_DefinesTimeScope) {
  // One timeunit + one timeprecision: valid time scope.
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// 52. timeunit and timeprecision work in interface declarations.
// §3.14.2.2: "... for any module, program, package, or interface
// definition ..."
TEST(ParserClause03, Cl3_14_2_2_WorksInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_TRUE(ifc->has_timeunit);
  EXPECT_TRUE(ifc->has_timeprecision);
  EXPECT_EQ(ifc->time_unit, TimeUnit::kUs);
  EXPECT_EQ(ifc->time_prec, TimeUnit::kNs);
}

// 53. timeunit and timeprecision work in program declarations.
// §3.14.2.2: "... for any module, program, package, or interface ..."
TEST(ParserClause03, Cl3_14_2_2_WorksInProgram) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 100ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* prog = r.cu->programs[0];
  EXPECT_TRUE(prog->has_timeunit);
  EXPECT_TRUE(prog->has_timeprecision);
  EXPECT_EQ(prog->time_unit, TimeUnit::kNs);
  EXPECT_EQ(prog->time_prec, TimeUnit::kPs);
}

// 54. All six time units are accepted as time literals for timeunit.
// §3.14.2.2 / §5.8: time literals can use s, ms, us, ns, ps, fs.
TEST(ParserClause03, Cl3_14_2_2_AllSixUnitsAccepted) {
  EXPECT_EQ(Parse("module m; timeunit 1s; endmodule").cu->modules[0]->time_unit,
            TimeUnit::kS);
  EXPECT_EQ(
      Parse("module m; timeunit 1ms; endmodule").cu->modules[0]->time_unit,
      TimeUnit::kMs);
  EXPECT_EQ(
      Parse("module m; timeunit 1us; endmodule").cu->modules[0]->time_unit,
      TimeUnit::kUs);
  EXPECT_EQ(
      Parse("module m; timeunit 1ns; endmodule").cu->modules[0]->time_unit,
      TimeUnit::kNs);
  EXPECT_EQ(
      Parse("module m; timeunit 1ps; endmodule").cu->modules[0]->time_unit,
      TimeUnit::kPs);
  EXPECT_EQ(
      Parse("module m; timeunit 1fs; endmodule").cu->modules[0]->time_unit,
      TimeUnit::kFs);
}

// 55. All three magnitudes (1, 10, 100) are accepted in timeunit.
// §3.14.2.2 / §5.8: time literals include magnitude.
TEST(ParserClause03, Cl3_14_2_2_AllThreeMagnitudes) {
  EXPECT_FALSE(Parse("module m; timeunit 1ns; endmodule").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 10ns; endmodule").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 100ns; endmodule").has_errors);
  // timeprecision with magnitudes.
  EXPECT_FALSE(Parse("module m; timeprecision 1ps; endmodule").has_errors);
  EXPECT_FALSE(Parse("module m; timeprecision 10ps; endmodule").has_errors);
  EXPECT_FALSE(Parse("module m; timeprecision 100ps; endmodule").has_errors);
}

// 56. timeunit keyword alone: only has_timeunit is set, not
// has_timeprecision.
TEST(ParserClause03, Cl3_14_2_2_TimeunitAloneNoPrec) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[0]->has_timeprecision);
}

// 57. timeprecision keyword alone: only has_timeprecision is set, not
// has_timeunit.
TEST(ParserClause03, Cl3_14_2_2_TimeprecisionAloneNoUnit) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// 58. Keywords must precede other items in the time scope.
// §3.14.2.2: "If specified, the timeunit and timeprecision declarations
// shall precede any other items in the current time scope."
// This test verifies timeunit before other items parses without error.
TEST(ParserClause03, Cl3_14_2_2_PrecedeOtherItems) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  logic x;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// 59. Repeated timeunit/timeprecision that match previous declaration.
// §3.14.2.2: "The timeunit and timeprecision declarations can be
// repeated as later items, but shall match the previous declaration
// within the current time scope."
TEST(ParserClause03, Cl3_14_2_2_RepeatMatchingDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  logic x;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
  EXPECT_EQ(r.cu->modules[0]->time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->modules[0]->time_prec, TimeUnit::kPs);
}

// 60. Separate modules each define their own time scope independently.
// §3.14.2.2: "There shall be at most one time unit and one time
// precision for any module ... definition."
TEST(ParserClause03, Cl3_14_2_2_SeparateModulesIndependentScope) {
  auto r = Parse(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->modules[0]->time_prec, TimeUnit::kPs);
  EXPECT_EQ(r.cu->modules[1]->time_unit, TimeUnit::kUs);
  EXPECT_EQ(r.cu->modules[1]->time_prec, TimeUnit::kNs);
}

// =============================================================================
// A.1.2 timeunits_declaration — all 4 forms
// =============================================================================
// Form 1: timeunit time_literal ;
TEST(SourceText, TimeunitOnly) {
  auto r = Parse("module m; timeunit 1ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

// Form 2: timeprecision time_literal ;
TEST(SourceText, TimeprecisionOnly) {
  auto r = Parse("module m; timeprecision 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 3: timeunit time_literal / time_literal ;
TEST(SourceText, TimeunitWithSlash) {
  auto r = Parse("module m; timeunit 1ns / 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 4: both timeunit and timeprecision separately.
TEST(SourceText, TimeunitAndTimeprecisionSeparate) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
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

static ParseResult3140203 Parse(const std::string& src) {
  ParseResult3140203 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
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

static ModuleDecl* FindNestedModule(const std::vector<ModuleItem*>& items) {
  for (auto* item : items)
    if (item->kind == ModuleItemKind::kNestedModuleDecl)
      return item->nested_module_decl;
  return nullptr;
}

// =============================================================================
// LRM §3.14.2.3 — Precedence of timeunit, timeprecision, and `timescale
// =============================================================================
// 1. Module with explicit timeunit — highest priority, no fallback needed.
TEST(ParserClause03, Cl3_14_2_3_ExplicitTimeunitTakesPriority) {
  auto r = Parse(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kPs);
}

// 2. Module with explicit timeprecision — highest priority.
TEST(ParserClause03, Cl3_14_2_3_ExplicitTimeprecisionTakesPriority) {
  auto r = Parse(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kFs);
}

// 3. Rule (a): Nested module inherits time unit from enclosing module.
TEST(ParserClause03, Cl3_14_2_3_RuleA_NestedInheritsUnit) {
  auto r = Parse(
      "module outer;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0];
  auto outer_resolved = ResolveModuleTimescale(outer, r.cu, false, {}, nullptr);
  EXPECT_TRUE(outer_resolved.has_unit);
  EXPECT_EQ(outer_resolved.unit, TimeUnit::kPs);

  // Find the nested module.
  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  EXPECT_FALSE(inner->has_timeunit);

  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, false, {}, &outer_resolved);
  EXPECT_TRUE(inner_resolved.has_unit);
  EXPECT_EQ(inner_resolved.unit, TimeUnit::kPs);
  EXPECT_TRUE(inner_resolved.has_precision);
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kFs);
}

// 4. Rule (a): Nested interface inherits from enclosing interface.
TEST(ParserClause03, Cl3_14_2_3_RuleA_NestedInterfaceInherits) {
  auto r = Parse(
      "interface outer_if;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  interface inner_if;\n"
      "  endinterface\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->interfaces[0];
  auto outer_resolved = ResolveModuleTimescale(outer, r.cu, false, {}, nullptr);

  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, false, {}, &outer_resolved);
  EXPECT_EQ(inner_resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kNs);
}

// 5. Rule (b): Module without timeunit falls back to `timescale.
TEST(ParserClause03, Cl3_14_2_3_RuleB_FallbackToTimescale) {
  auto r = Parse(
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.has_preproc_timescale);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kPs);
}

// 6. Rule (c): Module without timeunit or `timescale uses CU-scope timeunit.
TEST(ParserClause03, Cl3_14_2_3_RuleC_FallbackToCUTimeunit) {
  auto r = Parse(
      "timeunit 1ps;\n"
      "timeprecision 1fs;\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kPs);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kFs);

  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_TRUE(resolved.has_unit);
  EXPECT_EQ(resolved.unit, TimeUnit::kPs);
  EXPECT_TRUE(resolved.has_precision);
  EXPECT_EQ(resolved.precision, TimeUnit::kFs);
}

// 7. Rule (d): Default time unit when nothing is specified.
TEST(ParserClause03, Cl3_14_2_3_RuleD_DefaultTimeUnit) {
  auto r = Parse(
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_FALSE(resolved.has_unit);
  EXPECT_FALSE(resolved.has_precision);
  // Default is kNs (implementation-specific).
  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

// 8. CU-scope timeunit can only be set by keyword, not `timescale.
// §3.14.2.3: "The time unit of the compilation-unit scope can only be
// set by a timeunit declaration, not a `timescale directive."
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitOnlyByKeyword) {
  auto r = Parse(
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  // `timescale does NOT set CU-scope timeunit.
  EXPECT_FALSE(r.cu->has_cu_timeunit);
  EXPECT_FALSE(r.cu->has_cu_timeprecision);
}

// 9. Precedence: explicit timeunit > enclosing > `timescale > CU > default.
// Module has timeunit, enclosing has different, `timescale is different.
TEST(ParserClause03, Cl3_14_2_3_FullPrecedenceChain) {
  auto r = Parse(
      "`timescale 1ms / 1us\n"
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module outer;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  module inner;\n"
      "    timeunit 1fs;\n"
      "  endmodule\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0];
  auto outer_resolved = ResolveModuleTimescale(
      outer, r.cu, r.has_preproc_timescale, r.preproc_timescale, nullptr);
  // outer has explicit timeunit 1us.
  EXPECT_EQ(outer_resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(outer_resolved.precision, TimeUnit::kNs);

  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, &outer_resolved);
  // inner has explicit timeunit 1fs — that wins.
  EXPECT_EQ(inner_resolved.unit, TimeUnit::kFs);
  // inner has no timeprecision — inherits from enclosing (rule a).
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kNs);
}

// 10. Rule (b) takes precedence over rule (c).
TEST(ParserClause03, Cl3_14_2_3_TimescaleBeforeCUTimeunit) {
  auto r = Parse(
      "timeunit 1fs;\n"
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  // `timescale (rule b) takes precedence over CU timeunit (rule c).
  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(resolved.precision, TimeUnit::kPs);
}

// 11. CU-scope combined timeunit X / Y syntax.
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitSlashSyntax) {
  auto r = Parse(
      "timeunit 100ps / 10fs;\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kPs);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kFs);
}

// 12. Same precedence rules apply for timeprecision (§3.14.2.3).
TEST(ParserClause03, Cl3_14_2_3_SameRulesForPrecision) {
  // Module has no timeprecision, enclosing has it.
  auto r = Parse(
      "module outer;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  module inner;\n"
      "    timeunit 1ns;\n"
      "  endmodule\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0];
  auto outer_resolved = ResolveModuleTimescale(outer, r.cu, false, {}, nullptr);

  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, false, {}, &outer_resolved);
  // inner's precision comes from enclosing (rule a).
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kPs);
}

// 13. Default time unit is implementation-specific; ours is kNs.
TEST(ParserClause03, Cl3_14_2_3_DefaultIsImplementationSpecific) {
  auto r = Parse("module m; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

// 14. CU-scope timeunit applies to interface.
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitAppliesToInterface) {
  auto r = Parse(
      "timeunit 1ps;\n"
      "timeprecision 1fs;\n"
      "interface i;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->interfaces[0], r.cu, false, {}, nullptr);
  EXPECT_EQ(resolved.unit, TimeUnit::kPs);
  EXPECT_EQ(resolved.precision, TimeUnit::kFs);
}

// 15. CU-scope timeunit applies to program.
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitAppliesToProgram) {
  auto r = Parse(
      "timeunit 1us;\n"
      "timeprecision 1ns;\n"
      "program p;\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->programs[0], r.cu, false, {}, nullptr);
  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

// 16. Programs and packages cannot be nested (§3.14.2.3 rule a note).
// Only modules and interfaces can inherit via nesting.
TEST(ParserClause03, Cl3_14_2_3_ProgramsCannotBeNested) {
  // A standalone program without timeunit uses CU scope or default.
  auto r = Parse(
      "program p;\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->programs[0], r.cu, false, {}, nullptr);
  // No enclosing, no `timescale, no CU timeunit → default.
  EXPECT_FALSE(resolved.has_unit);
}

// 17. Multiple modules — each independently resolves time.
TEST(ParserClause03, Cl3_14_2_3_IndependentResolution) {
  auto r = Parse(
      "`timescale 1us / 1ps\n"
      "module a;\n"
      "  timeunit 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved_a =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  auto resolved_b =
      ResolveModuleTimescale(r.cu->modules[1], r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, nullptr);
  // a has explicit timeunit.
  EXPECT_EQ(resolved_a.unit, TimeUnit::kNs);
  // b falls back to `timescale.
  EXPECT_EQ(resolved_b.unit, TimeUnit::kUs);
  EXPECT_EQ(resolved_b.precision, TimeUnit::kPs);
}

// 18. Nested module with own timeunit overrides inheritance.
TEST(ParserClause03, Cl3_14_2_3_NestedOverridesInheritance) {
  auto r = Parse(
      "module outer;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  module inner;\n"
      "    timeunit 1fs;\n"
      "    timeprecision 1fs;\n"
      "  endmodule\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0];
  auto outer_resolved = ResolveModuleTimescale(outer, r.cu, false, {}, nullptr);

  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, false, {}, &outer_resolved);
  // inner has own timeunit/timeprecision — these override.
  EXPECT_EQ(inner_resolved.unit, TimeUnit::kFs);
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kFs);
}

// Helper: preprocess and parse, returning CU + preprocessor state.
struct ParseResult31403 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
  TimeScale preproc_timescale;
  bool has_preproc_timescale = false;
  TimeUnit preproc_global_precision = TimeUnit::kNs;
};

static ParseResult31403 Parse(const std::string& src) {
  ParseResult31403 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
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

// =============================================================================
// LRM §3.14.3 — Simulation time unit (global time precision)
// =============================================================================
// 19. Global precision is minimum of all timeprecision statements.
TEST(ParserClause03, Cl3_14_3_MinOfTimeprecisionStatements) {
  auto r = Parse(
      "module a;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module c;\n"
      "  timeprecision 1us;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kPs);  // min of ns, ps, us = ps
}

// 20. Global precision considers timeunit precision argument (slash syntax).
TEST(ParserClause03, Cl3_14_3_ConsidersTimeunitPrecArg) {
  auto r = Parse(
      "module a;\n"
      "  timeunit 1us / 1fs;\n"
      "endmodule\n"
      "module b;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gp = ComputeGlobalTimePrecision(r.cu, r.has_preproc_timescale,
                                       r.preproc_global_precision);
  EXPECT_EQ(gp, TimeUnit::kFs);  // min of fs, ns = fs
}

}  // namespace
