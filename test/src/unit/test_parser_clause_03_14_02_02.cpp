// §3.14.2.2: The timeunit and timeprecision keywords

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
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
static ParseResult ParseTimescale31402(const std::string& src) {
  ParseResult result;
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

// 49. LRM Example E: timeunit with optional second argument.
// §3.14.2.2:
//   module E (...);
//     timeunit 100ps / 10fs;
TEST(ParserClause03, Cl3_14_2_2_LrmExampleE) {
  auto r = ParseTimescale31402(
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
  auto r1 = ParseTimescale31402(
      "`timescale 1us / 1ns\n"
      "module m;\n"
      "  timeunit 1ps;\n"
      "  timeprecision 1fs;\n"
      "endmodule\n");
  auto r2 = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

// 55. All three magnitudes (1, 10, 100) are accepted in timeunit.
// §3.14.2.2 / §5.8: time literals include magnitude.
TEST(ParserClause03, Cl3_14_2_2_AllThreeMagnitudes) {
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeunit 1ns; endmodule").has_errors);
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeunit 10ns; endmodule").has_errors);
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeunit 100ns; endmodule").has_errors);
  // timeprecision with magnitudes.
  EXPECT_FALSE(
      ParseTimescale31402("module m; timeprecision 1ps; endmodule").has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeprecision 10ps; endmodule")
                   .has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeprecision 100ps; endmodule")
                   .has_errors);
}

// 56. timeunit keyword alone: only has_timeunit is set, not
// has_timeprecision.
TEST(ParserClause03, Cl3_14_2_2_TimeunitAloneNoPrec) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402("module m; timeunit 1ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

// Form 2: timeprecision time_literal ;
TEST(SourceText, TimeprecisionOnly) {
  auto r = ParseTimescale31402("module m; timeprecision 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 3: timeunit time_literal / time_literal ;
TEST(SourceText, TimeunitWithSlash) {
  auto r = ParseTimescale31402("module m; timeunit 1ns / 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 4: both timeunit and timeprecision separately.
TEST(SourceText, TimeunitAndTimeprecisionSeparate) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// 11. CU-scope combined timeunit X / Y syntax.
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitSlashSyntax) {
  auto r = ParseTimescale31402(
      "timeunit 100ps / 10fs;\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kPs);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kFs);
}

}  // namespace
