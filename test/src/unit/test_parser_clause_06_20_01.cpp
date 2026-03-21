#include "fixture_elaborator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParameterPortListParsing,ParamPortDataTypeForm) {
  auto r = Parse("module m #(int WIDTH = 8); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "WIDTH");
}

TEST(ParameterPortListParsing,ParamPortMixedForms) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 2,\n"
      "           type T = logic, int C = 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
  EXPECT_EQ(r.cu->modules[0]->params[2].first, "T");
  EXPECT_EQ(r.cu->modules[0]->params[3].first, "C");
}

TEST(ExpressionParsing, ParamExprBinaryOp) {
  auto r = Parse(
      "module m #(parameter int P = 2 * 8);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind, ExprKind::kBinary);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsSingle) {
  auto r = Parse("module m; parameter int A = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsMultiple) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(DeclarationAssignmentParsing, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, TypeAssignmentWithDefault) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterPortListParsing,ParamPortLocalparam) {
  auto r = Parse("module m #(localparam int X = 5); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "X");
}

TEST(ModuleParamsParsing, TypedParamPort) {
  auto r = Parse(
      "module m #(parameter int W = 8, int D = 4)(\n"
      "  input logic [W-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 2u);
}

TEST(ParameterPortListParsing, EmptyParameterPortListParses) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 0u);
}

TEST(ParameterDeclarations, CompilationUnitParameterParses) {
  auto r = Parse("parameter int X = 42;\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "X");
}

TEST(ParameterDeclarations, ParameterAndLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int param_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) param_count++;
  }
  EXPECT_EQ(param_count, 2);
}

}  // namespace
