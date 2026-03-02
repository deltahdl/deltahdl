// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Defparam tests ---
TEST(Parser, DefparamSingle) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1);
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(Parser, DefparamMultiple) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8, u1.DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2);
}

// parameter_override: defparam list_of_defparam_assignments.
TEST(SourceText, ParameterOverrideDefparam) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  defparam sub.W = 16, sub.D = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  auto* dp = r.cu->modules[0]->items[0];
  EXPECT_EQ(dp->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(dp->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.3 Declaration lists
// =============================================================================
// --- list_of_defparam_assignments ---
// defparam_assignment { , defparam_assignment }
TEST(ParserA23, ListOfDefparamAssignmentsSingle) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 1u);
}

TEST(ParserA23, ListOfDefparamAssignmentsMultiple) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.WIDTH = 16, u1.DEPTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2u);
}

// =============================================================================
// A.2.4 Declaration assignments
// =============================================================================
// --- defparam_assignment ---
// hierarchical_parameter_identifier = constant_mintypmax_expression
TEST(ParserA24, DefparamAssignmentHierarchical) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.sub.WIDTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
  // The path expression should be a hierarchical reference
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(ParserA24, DefparamAssignmentMintypmax) {
  // constant_mintypmax_expression: expr : expr : expr
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  defparam u0.DELAY = 1:2:3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1u);
}

// =============================================================================
// A.1.2 bind_directive (§23.11)
// =============================================================================
// Form 1: bind target_scope bind_instantiation
TEST(SourceText, BindDirectiveBasic) {
  auto r =
      ParseWithPreprocessor("bind target_mod checker_mod chk_inst(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target_mod");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
  ASSERT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_module,
            "checker_mod");
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_name, "chk_inst");
}

// Form 1 with instance list: bind scope : inst1, inst2 instantiation
TEST(SourceText, BindDirectiveWithInstanceList) {
  auto r = ParseWithPreprocessor("bind dut : i1, i2 chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "i1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "i2");
}

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = ParseWithPreprocessor("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

}  // namespace
