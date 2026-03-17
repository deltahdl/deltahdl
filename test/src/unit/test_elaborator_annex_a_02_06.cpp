#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- function_declaration ---

TEST(FunctionDeclElaboration, FunctionDeclAddedToModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->function_decls.size(), 1u);
}

TEST(FunctionDeclElaboration, FunctionDeclVoidReturn) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function void f(); endfunction\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, FunctionDeclLifetimeAutomatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int f(); return 0; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_automatic);
}

TEST(FunctionDeclElaboration, FunctionDeclLifetimeStatic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function static int f(); return 0; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  EXPECT_TRUE(mod->function_decls[0]->is_static);
}

// --- function_body_declaration: implicit return type ---

TEST(FunctionDeclElaboration, FunctionImplicitReturnType) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function [7:0] f(); return 8'hFF; endfunction\n"
      "endmodule\n"));
}

// --- function_body_declaration: old-style ports ---

TEST(FunctionDeclElaboration, FunctionOldStylePorts) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function int f;\n"
      "    input int a;\n"
      "    f = a + 1;\n"
      "  endfunction\n"
      "endmodule\n"));
}

// --- dpi_import_export ---

TEST(FunctionDeclElaboration, DpiImportFunctionElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiImportTaskElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" task c_task(int x);\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiImportPureElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" pure function int pure_func(int x);\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiImportContextElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" context function void ctx_func();\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiImportTaskContextElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  import \"DPI-C\" context task ctx_task();\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiExportFunctionElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function void my_func(); endfunction\n"
      "  export \"DPI-C\" function my_func;\n"
      "endmodule\n"));
}

TEST(FunctionDeclElaboration, DpiExportTaskElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  task my_task(); endtask\n"
      "  export \"DPI-C\" task my_task;\n"
      "endmodule\n"));
}

// --- multiple function declarations ---

TEST(FunctionDeclElaboration, MultipleFunctionsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int f1(); return 1; endfunction\n"
      "  function int f2(); return 2; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->function_decls.size(), 2u);
}

}  // namespace
