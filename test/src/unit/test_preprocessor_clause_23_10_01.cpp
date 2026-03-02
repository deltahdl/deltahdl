// §23.10.1: defparam statement

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

}  // namespace
