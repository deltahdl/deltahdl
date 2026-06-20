#include "fixture_elaborator.h"

using namespace delta;

TEST(CompilationUnitElaboration, ElabModuleWithCuFunction) {
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeFunctionInDesign) {
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

TEST(CompilationUnitElaboration, CuScopeTypedefVisibleInModule) {
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

TEST(CompilationUnitElaboration, CuScopeTypedefTypeWidth) {
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

TEST(CompilationUnitElaboration, CuScopeLocalparamElaborates) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, DollarUnitScopeExprElaborates) {
  EXPECT_TRUE(
      ElabOk("bit b;\n"
             "module m;\n"
             "  logic sig;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeClassVisibleInModule) {
  EXPECT_TRUE(
      ElabOk("class my_class;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  my_class obj;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeItemsInSourceOrder) {
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

TEST(CompilationUnitElaboration, MultipleCuScopeTypedefs) {
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
TEST(CompilationUnitElaboration, CuScopeTaskElaboratesSuccessfully) {
  EXPECT_TRUE(
      ElabOk("task my_task;\n"
             "endtask\n"
             "module m; endmodule\n"));
}

TEST(CompilationUnitElaboration, LocalScopeShadowsCuScopeLocalparam) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  localparam int WIDTH = 16;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeLocalparamVisibleInMultipleModules) {
  ElabFixture f;
  auto* design = Elaborate(
      "localparam int WIDTH = 8;\n"
      "module sub;\n"
      "  logic [WIDTH-1:0] b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [WIDTH-1:0] a;\n"
      "  sub u1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CompilationUnitElaboration, CuScopeVarDeclElaborates) {
  EXPECT_TRUE(
      ElabOk("int global_counter;\n"
             "module m;\n"
             "  logic sig;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, ForwardReferenceToCuScopeFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int observed;\n"
             "  initial observed = helper(5);\n"
             "endmodule\n"
             "function int helper(int x); return x + 1; endfunction\n"));
}

TEST(CompilationUnitElaboration, ForwardReferenceToCuScopeTaskAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial later_task();\n"
             "endmodule\n"
             "task later_task; endtask\n"));
}
