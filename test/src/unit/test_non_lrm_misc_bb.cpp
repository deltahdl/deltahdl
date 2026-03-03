// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

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

static ModuleDecl* FindNestedModule(const std::vector<ModuleItem*>& items) {
  for (auto* item : items)
    if (item->kind == ModuleItemKind::kNestedModuleDecl)
      return item->nested_module_decl;
  return nullptr;
}

namespace {

// 5. Rule (b): Module without timeunit falls back to `timescale.
TEST(ParserClause03, Cl3_14_2_3_RuleB_FallbackToTimescale) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

// 12. Same precedence rules apply for timeprecision (§3.14.2.3).
TEST(ParserClause03, Cl3_14_2_3_SameRulesForPrecision) {
  // Module has no timeprecision, enclosing has it.
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402("module m; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

// 14. CU-scope timeunit applies to interface.
TEST(ParserClause03, Cl3_14_2_3_CUTimeunitAppliesToInterface) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

// =============================================================================
// LRM §3.14.3 — Simulation time unit (global time precision)
// =============================================================================
// 19. Global precision is minimum of all timeprecision statements.
TEST(ParserClause03, Cl3_14_3_MinOfTimeprecisionStatements) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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
