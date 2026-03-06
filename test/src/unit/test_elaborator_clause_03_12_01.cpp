#include "fixture_elaborator.h"

using namespace delta;

TEST(ElabClause03, Cl3_12_1_ElabModuleWithCuFunction) {
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_12_1_CuScopeFunctionInDesign) {
  ElabFixture f;
  auto* design = Elaborate(
      "function int helper(int x); return x + 1; endfunction\n"
      "task auto_task; endtask\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->cu_function_decls.size(), 2u);
  EXPECT_EQ(design->cu_function_decls[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(design->cu_function_decls[0]->name, "helper");
  EXPECT_EQ(design->cu_function_decls[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(design->cu_function_decls[1]->name, "auto_task");
}

TEST(ElabClause03, Cl3_12_1_CuScopeTypedefVisibleInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [15:0] word_t;\n"
      "module m;\n"
      "  word_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "data");
  EXPECT_EQ(mod->variables[0].width, 16u);
}

TEST(ElabClause03, Cl3_12_1_CuScopeTypedefTypeWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [7:0] byte_t;\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->type_widths.find("byte_t");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 8u);
}

TEST(ElabClause03, Cl3_12_1_CuScopeLocalparamElaborates) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_12_1_DollarUnitScopeExprElaborates) {
  EXPECT_TRUE(
      ElabOk("bit b;\n"
             "module m;\n"
             "  logic sig;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_12_1_CuScopeClassVisibleInModule) {
  EXPECT_TRUE(
      ElabOk("class my_class;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  my_class obj;\n"
             "endmodule\n"));
}

TEST(ElabClause03, Cl3_12_1_CuScopeItemsInSourceOrder) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef int first_t;\n"
      "function int second_func(int x); return x; endfunction\n"
      "localparam int THIRD = 3;\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabClause03, Cl3_12_1_MultipleCuScopeTypedefs) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [7:0] byte_t;\n"
      "typedef logic [31:0] word_t;\n"
      "module m;\n"
      "  byte_t a;\n"
      "  word_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[1].width, 32u);
}
