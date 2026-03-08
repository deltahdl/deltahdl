#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"
#include "parser/time_resolve.h"

using namespace delta;

namespace {

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

TEST(ParserClause03, Cl3_14_2_3_RuleD_DefaultTimeUnit) {
  auto r = ParseTimescale31402(
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_FALSE(resolved.has_unit);
  EXPECT_FALSE(resolved.has_precision);

  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

TEST(ParserClause03, Cl3_14_2_3_CUTimeunitOnlyByKeyword) {
  auto r = ParseTimescale31402(
      "`timescale 1us / 1ps\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_FALSE(r.cu->has_cu_timeunit);
  EXPECT_FALSE(r.cu->has_cu_timeprecision);
}

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

  EXPECT_EQ(outer_resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(outer_resolved.precision, TimeUnit::kNs);

  auto* inner = FindNestedModule(outer->items);
  ASSERT_NE(inner, nullptr);
  auto inner_resolved =
      ResolveModuleTimescale(inner, r.cu, r.has_preproc_timescale,
                             r.preproc_timescale, &outer_resolved);

  EXPECT_EQ(inner_resolved.unit, TimeUnit::kFs);

  EXPECT_EQ(inner_resolved.precision, TimeUnit::kNs);
}

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

  EXPECT_EQ(resolved.unit, TimeUnit::kUs);
  EXPECT_EQ(resolved.precision, TimeUnit::kPs);
}

TEST(ParserClause03, Cl3_14_2_3_SameRulesForPrecision) {
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

  EXPECT_EQ(inner_resolved.precision, TimeUnit::kPs);
}

TEST(ParserClause03, Cl3_14_2_3_DefaultIsImplementationSpecific) {
  auto r = ParseTimescale31402("module m; endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->modules[0], r.cu, false, {}, nullptr);
  EXPECT_EQ(resolved.unit, TimeUnit::kNs);
  EXPECT_EQ(resolved.precision, TimeUnit::kNs);
}

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

TEST(ParserClause03, Cl3_14_2_3_ProgramsCannotBeNested) {
  auto r = ParseTimescale31402(
      "program p;\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
  auto resolved =
      ResolveModuleTimescale(r.cu->programs[0], r.cu, false, {}, nullptr);

  EXPECT_FALSE(resolved.has_unit);
}

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

  EXPECT_EQ(resolved_a.unit, TimeUnit::kNs);

  EXPECT_EQ(resolved_b.unit, TimeUnit::kUs);
  EXPECT_EQ(resolved_b.precision, TimeUnit::kPs);
}

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

  EXPECT_EQ(inner_resolved.unit, TimeUnit::kFs);
  EXPECT_EQ(inner_resolved.precision, TimeUnit::kFs);
}

}
