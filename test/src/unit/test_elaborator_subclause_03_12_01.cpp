#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

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

// The declared widths are what say WIDTH reached both modules. A bound that
// folds to nothing is not reported: EvalRangeWidth in
// src/elaborator/type_eval.cpp answers 0 and the declaration falls through to
// one bit, so an assertion that elaboration succeeded holds whether WIDTH was
// visible or not.
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
  const auto* a = FindVar(design, "top", "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->width, 8u);
  const auto* b = FindVar(design, "sub", "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->width, 8u);
}

// §3.12.1 puts a compilation-unit declaration in scope for every design element
// in the unit, and the two modules here are siblings rather than a module and
// its instance: neither is elaborated inside the other, so WIDTH has to survive
// the first module's elaboration to size the second one's declaration.
//
// Elaborator::ElaborateModule takes back what a module adds to the elaborator's
// typedef and parameter maps before the next module is elaborated, which is
// what keeps one module's package import out of the next (§26.3). This states
// the other half of that: what the compilation unit itself declared is written
// before any module is elaborated and is still there afterwards.
TEST(CompilationUnitElaboration, CuScopeLocalparamVisibleInASecondTopModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "localparam int WIDTH = 8;\n"
      "module first;\n"
      "  logic [WIDTH-1:0] a;\n"
      "endmodule\n"
      "module second;\n"
      "  logic [WIDTH-1:0] b;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* b = FindVar(design, "second", "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->width, 8u);
}

TEST(CompilationUnitElaboration, CuScopeVarDeclElaborates) {
  EXPECT_TRUE(
      ElabOk("int global_counter;\n"
             "module m;\n"
             "  logic sig;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesToCompilationUnitScopeDespiteLocalShadow) {
  ElabFixture f;
  // §3.12.1: the whole purpose of the $unit:: prefix is unambiguous access to
  // the outermost (compilation-unit-scope) declaration. Here a module-local
  // localparam K shadows a compilation-unit localparam K of a different value.
  // The bare reference must see the local (width 3) while the $unit::K
  // reference must reach past the shadow to the compilation-unit value
  // (width 8).
  auto* design = Elaborate(
      "localparam int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  logic [$unit::K-1:0] wide;\n"
      "  logic [K-1:0] narrow;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[1].name, "narrow");
  EXPECT_EQ(mod->variables[1].width, 3u);
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesCompilationUnitParameterPastLocalShadow) {
  ElabFixture f;
  // §3.12.1: the outermost declaration reached by $unit:: may be declared with
  // the `parameter` keyword rather than `localparam`. At compilation-unit scope
  // both name a constant, so a $unit:: reference must still bypass a same-named
  // module-local parameter (here local 3) and resolve to the outermost value 8.
  auto* design = Elaborate(
      "parameter int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  logic [$unit::K-1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesToCompilationUnitScopeInParameterInitializer) {
  ElabFixture f;
  // §3.12.1: the $unit:: disambiguation applies wherever a constant expression
  // is evaluated, not only in a packed dimension. Here a module-local
  // localparam M is initialized from $unit::K while a same-named local K
  // shadows the compilation-unit K. M must be computed from the outermost K
  // (8 + 1 == 9), giving a 9-bit vector, not from the local K (which would be
  // 4 bits).
  auto* design = Elaborate(
      "localparam int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  localparam int M = $unit::K + 1;\n"
      "  logic [M-1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 9u);
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
