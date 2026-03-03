// §3.14.2.3: Precedence of timeunit, timeprecision, and `timescale

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

namespace {

// =============================================================================
// LRM §3.14.2.3 — Precedence of timeunit, timeprecision, and `timescale
// =============================================================================
// 1. Module with explicit timeunit — highest priority, no fallback needed.
TEST(ParserClause03, Cl3_14_2_3_ExplicitTimeunitTakesPriority) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

static ModuleDecl* FindNestedModule(const std::vector<ModuleItem*>& items) {
  for (auto* item : items)
    if (item->kind == ModuleItemKind::kNestedModuleDecl)
      return item->nested_module_decl;
  return nullptr;
}

// 3. Rule (a): Nested module inherits time unit from enclosing module.
TEST(ParserClause03, Cl3_14_2_3_RuleA_NestedInheritsUnit) {
  auto r = ParseTimescale31402(
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
  auto r = ParseTimescale31402(
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

}  // namespace
