#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, DescriptionPackageItemTask) {
  auto r = Parse("task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

TEST(ParserClause03, Cl3_12_1_ForwardRefSyntaxValid) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

TEST(Parser, PackageAndModule) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}
TEST(ParserSection23, MultipleModuleDefinitions) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(ParserSection18, TopLevelFunction) {
  auto r = Parse(
      "function int my_func(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "class C;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserClause03, Cl3_12_1_CuScopeTypedef) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(r.cu->cu_items[0]->name, "myint");
}

TEST(ParserClause03, Cl3_12_1_CuScopeLocalparam) {
  auto r = Parse(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "WIDTH");
}

TEST(ParserClause03, Cl3_12_1_CuScopeParameter) {
  auto r = Parse(
      "parameter int DEPTH = 16;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "DEPTH");
}

TEST(ParserClause03, Cl3_12_1_CuScopeImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "import pkg::*;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserClause03, Cl3_12_1_CuScopeDataDecl) {
  auto r = Parse(
      "bit b;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "b");
}

TEST(ParserClause03, Cl3_12_1_DollarUnitScopeResolutionExpr) {
  auto r = Parse(
      "bit b;\n"
      "module m;\n"
      "  initial b = $unit::b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_FALSE(mod->items.empty());
  auto* initial = mod->items.back();
  ASSERT_NE(initial->body, nullptr);
  auto* assign_stmt = initial->body;
  ASSERT_NE(assign_stmt->rhs, nullptr);
  EXPECT_EQ(assign_stmt->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(assign_stmt->rhs->text, "b");
  EXPECT_EQ(assign_stmt->rhs->scope_prefix, "$unit");
}

TEST(ParserClause03, Cl3_12_1_DollarUnitScopeInAssignment) {
  EXPECT_TRUE(
      ParseOk("task t;\n"
              "  int b;\n"
              "  b = 5 + $unit::b;\n"
              "endtask\n"
              "module m; endmodule\n"));
}

TEST(ParserClause03, Cl3_12_1_MultipleCuScopeItems) {
  auto r = Parse(
      "typedef logic [7:0] byte_t;\n"
      "localparam int N = 4;\n"
      "function int helper(int x); return x; endfunction\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 3u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[2]->kind, ModuleItemKind::kFunctionDecl);
}

}
