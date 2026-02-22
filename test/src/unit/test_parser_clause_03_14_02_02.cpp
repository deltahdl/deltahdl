#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Helper: parse source and return the compilation unit.
struct ParseResult3140202 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult3140202 Parse(const std::string &src) {
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
  auto *mod = r.cu->modules[0];
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
  auto *mod = r.cu->modules[0];
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
  auto *mod = r.cu->modules[0];
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
  auto *mod = r.cu->modules[0];
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
  auto *mod = r.cu->modules[0];
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
  auto *ifc = r.cu->interfaces[0];
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
  auto *prog = r.cu->programs[0];
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
