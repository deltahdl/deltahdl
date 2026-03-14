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

TEST(DesignBuildingBlockParsing, ForwardRefSyntaxValid) {
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
TEST(ModuleAndHierarchyParsing, MultipleModuleDefinitions) {
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

TEST(ConstrainedRandomParsing, TopLevelFunction) {
  auto r = Parse(
      "function int my_func(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "class C;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(DesignBuildingBlockParsing, CuScopeTypedef) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(r.cu->cu_items[0]->name, "myint");
}

TEST(DesignBuildingBlockParsing, CuScopeLocalparam) {
  auto r = Parse(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "WIDTH");
}

TEST(DesignBuildingBlockParsing, CuScopeParameter) {
  auto r = Parse(
      "parameter int DEPTH = 16;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "DEPTH");
}

TEST(DesignBuildingBlockParsing, CuScopeImport) {
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

TEST(DesignBuildingBlockParsing, CuScopeDataDecl) {
  auto r = Parse(
      "bit b;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "b");
}

TEST(DesignBuildingBlockParsing, DollarUnitScopeResolutionExpr) {
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

TEST(DesignBuildingBlockParsing, DollarUnitScopeInAssignment) {
  EXPECT_TRUE(
      ParseOk("task t;\n"
              "  int b;\n"
              "  b = 5 + $unit::b;\n"
              "endtask\n"
              "module m; endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MultipleCuScopeItems) {
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

// §3.1 General — the compilation unit must accept empty, whitespace-only,
// and comment-only sources as valid, producing a CU with all building-block
// vectors empty.
TEST(CompilationUnitStructure, EmptySourceProducesValidCompilationUnit) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
  EXPECT_TRUE(r.cu->classes.empty());
  EXPECT_TRUE(r.cu->cu_items.empty());
}

TEST(CompilationUnitStructure,
     WhitespaceOnlySourceProducesValidCompilationUnit) {
  auto r = Parse("   \t\n\n  \t  ");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(CompilationUnitStructure,
     LineCommentOnlySourceProducesValidCompilationUnit) {
  auto r = Parse("// this file is intentionally empty\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(CompilationUnitStructure,
     BlockCommentOnlySourceProducesValidCompilationUnit) {
  auto r = Parse("/* nothing here */");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(CompilationUnitStructure,
     MixedWhitespaceAndCommentsProducesValidCompilationUnit) {
  auto r = Parse(
      "\n"
      "  // line comment\n"
      "\t/* block comment */\n"
      "  /* multi-line\n"
      "     block comment */\n"
      "\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(CompilationUnitStructure, DefaultFieldValues) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->default_nettype, NetType::kWire);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kNs);
  EXPECT_FALSE(r.cu->has_cu_timeunit);
  EXPECT_FALSE(r.cu->has_cu_timeprecision);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->bind_directives.empty());
}

TEST(CompilationUnitStructure, NullItemSemicolonAtTopLevel) {
  auto r = Parse(";;;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

TEST(CompilationUnitStructure, NullItemsBetweenDesignElements) {
  auto r = Parse(
      ";\n"
      "module m; endmodule\n"
      ";\n"
      "package p; endpackage\n"
      ";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

TEST(CompilationUnitStructure, MultipleModulesAccumulate) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(CompilationUnitStructure, PreservesInsertionOrder) {
  auto r = Parse(
      "module m1; endmodule\n"
      "package p1; endpackage\n"
      "module m2; endmodule\n"
      "package p2; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "m1");
  EXPECT_EQ(r.cu->modules[1]->name, "m2");
  EXPECT_EQ(r.cu->packages[0]->name, "p1");
  EXPECT_EQ(r.cu->packages[1]->name, "p2");
}

TEST(CompilationUnitStructure, UnrecognizedTopLevelTokenIsError) {
  EXPECT_FALSE(ParseOk("42"));
}

TEST(CompilationUnitStructure, MultiplePackagesAccumulate) {
  auto r = Parse(
      "package p1; endpackage\n"
      "package p2; endpackage\n"
      "package p3; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 3u);
  EXPECT_EQ(r.cu->packages[0]->name, "p1");
  EXPECT_EQ(r.cu->packages[1]->name, "p2");
  EXPECT_EQ(r.cu->packages[2]->name, "p3");
}

TEST(CompilationUnitStructure, MultipleInterfacesAccumulate) {
  auto r = Parse(
      "interface i1; endinterface\n"
      "interface i2; endinterface\n"
      "interface i3; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 3u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "i1");
  EXPECT_EQ(r.cu->interfaces[1]->name, "i2");
  EXPECT_EQ(r.cu->interfaces[2]->name, "i3");
}

TEST(CompilationUnitStructure, MultipleProgramsAccumulate) {
  auto r = Parse(
      "program p1; endprogram\n"
      "program p2; endprogram\n"
      "program p3; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 3u);
  EXPECT_EQ(r.cu->programs[0]->name, "p1");
  EXPECT_EQ(r.cu->programs[1]->name, "p2");
  EXPECT_EQ(r.cu->programs[2]->name, "p3");
}

TEST(CompilationUnitStructure, MultipleCheckersAccumulate) {
  auto r = Parse(
      "checker c1; endchecker\n"
      "checker c2; endchecker\n"
      "checker c3; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 3u);
  EXPECT_EQ(r.cu->checkers[0]->name, "c1");
  EXPECT_EQ(r.cu->checkers[1]->name, "c2");
  EXPECT_EQ(r.cu->checkers[2]->name, "c3");
}

TEST(CompilationUnitScope, FunctionGoesToCuItems) {
  auto r = Parse(
      "function int add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilationUnitStructure, TaskGoesToCuItems) {
  auto r = Parse(
      "task my_task;\n"
      "endtask\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(CompilationUnitStructure, SourceWithoutModulesIsValid) {
  auto r = Parse(
      "package p; endpackage\n"
      "interface ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
}

// §3.1 — UDPs (primitives) accumulate in the compilation unit.
TEST(CompilationUnitStructure, MultipleUdpsAccumulate) {
  auto r = Parse(
      "primitive u1(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 ? : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive u2(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->name, "u1");
  EXPECT_EQ(r.cu->udps[1]->name, "u2");
}

// §3.1 — Configs accumulate in the compilation unit.
TEST(CompilationUnitStructure, MultipleConfigsAccumulate) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg1;\n"
      "  design m;\n"
      "endconfig\n"
      "config cfg2;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 2u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
  EXPECT_EQ(r.cu->configs[1]->name, "cfg2");
}

// §3.1 — CU-scope classes accumulate in the compilation unit.
TEST(CompilationUnitStructure, CuScopeClassesAccumulate) {
  auto r = Parse(
      "class C1;\n"
      "  int x;\n"
      "endclass\n"
      "class C2;\n"
      "  int y;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "C1");
  EXPECT_EQ(r.cu->classes[1]->name, "C2");
}

// §3.1 — CU-scope items: multiple functions and tasks accumulate.
TEST(CompilationUnitStructure, MultipleCuScopeSubroutinesAccumulate) {
  auto r = Parse(
      "function void f1; endfunction\n"
      "function void f2; endfunction\n"
      "task t1; endtask\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 3u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// §3.1 — CU-scope typedef is stored in cu_items.
TEST(CompilationUnitStructure, CuScopeTypedefGoesToCuItems) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

// §3.1 — CU-scope import is stored in cu_items.
TEST(CompilationUnitStructure, CuScopeImportGoesToCuItems) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "import pkg::*;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

// §3.1 — CU-scope variable declaration is stored in cu_items.
TEST(CompilationUnitStructure, CuScopeVarDeclGoesToCuItems) {
  auto r = Parse(
      "int global_var;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

}  // namespace
