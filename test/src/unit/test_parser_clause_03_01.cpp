// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(CompilationUnitStructure, CuScopeFunctionGoesToCuItems) {
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

TEST(CompilationUnitStructure, CuScopeTaskGoesToCuItems) {
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

// §3.1 — All seven design element types coexist in a single compilation unit.
TEST(CompilationUnitStructure, AllDesignElementTypesCoexist) {
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive u(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
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

// §3.1 — CU-scope parameter declaration is stored in cu_items.
TEST(CompilationUnitStructure, CuScopeParameterGoesToCuItems) {
  auto r = Parse(
      "parameter int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

// §3.1 — End labels on design elements parse correctly.
TEST(CompilationUnitStructure, ModuleEndLabel) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(CompilationUnitStructure, PackageEndLabel) {
  auto r = Parse("package bar; endpackage : bar\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "bar");
}

TEST(CompilationUnitStructure, InterfaceEndLabel) {
  auto r = Parse("interface baz; endinterface : baz\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "baz");
}

TEST(CompilationUnitStructure, ProgramEndLabel) {
  auto r = Parse("program qux; endprogram : qux\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "qux");
}

TEST(CompilationUnitStructure, CheckerEndLabel) {
  auto r = Parse("checker ck; endchecker : ck\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "ck");
}

// §3.1 — Error: missing end-keyword.
TEST(CompilationUnitStructure, MissingEndmoduleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

TEST(CompilationUnitStructure, MissingEndpackageIsError) {
  EXPECT_FALSE(ParseOk("package p;"));
}

TEST(CompilationUnitStructure, MissingEndinterfaceIsError) {
  EXPECT_FALSE(ParseOk("interface i;"));
}

TEST(CompilationUnitStructure, MissingEndprogramIsError) {
  EXPECT_FALSE(ParseOk("program p;"));
}

TEST(CompilationUnitStructure, MissingEndcheckerIsError) {
  EXPECT_FALSE(ParseOk("checker c;"));
}

// §3.1 — Error: mismatched end label.
TEST(CompilationUnitStructure, MismatchedEndLabelIsError) {
  EXPECT_FALSE(ParseOk("module foo; endmodule : bar\n"));
}

// §3.1 — Module with design element name containing underscores and digits.
TEST(CompilationUnitStructure, DesignElementNameWithUnderscoresAndDigits) {
  auto r = Parse("module my_module_123; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_module_123");
}

// §3.1 — Design elements with comments interspersed.
TEST(CompilationUnitStructure, CommentsInterspersedBetweenDesignElements) {
  auto r = Parse(
      "// header comment\n"
      "module m; endmodule\n"
      "/* between */\n"
      "package p; endpackage\n"
      "// trailer\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

// §3.1 — Design elements and CU-scope items interleaved.
TEST(CompilationUnitStructure, DesignElementsAndCuItemsInterleaved) {
  auto r = Parse(
      "function void f1; endfunction\n"
      "module m1; endmodule\n"
      "task t1; endtask\n"
      "package p1; endpackage\n"
      "function void f2; endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->cu_items.size(), 3u);
}

// §3.1 — Large number of modules accumulate correctly.
TEST(CompilationUnitStructure, ManyModulesAccumulate) {
  std::string src;
  for (int i = 0; i < 50; ++i) {
    src += "module m" + std::to_string(i) + "; endmodule\n";
  }
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 50u);
}

TEST(CompilationUnitStructure, TimeunitDeclarationSetsFlag) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
}

TEST(CompilationUnitStructure, TimeprecisionDeclarationSetsFlag) {
  auto r = Parse(
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(CompilationUnitStructure, TimeunitAndTimeprecisionBothSet) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
}

TEST(CompilationUnitStructure, CuScopeLocalparamGoesToCuItems) {
  auto r = Parse(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->cu_items.size(), 1u);
}

TEST(CompilationUnitStructure, ModuleWithEmptyPortListParens) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(CompilationUnitStructure, BindDirectiveGoesToBindDirectives) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "bind target binder b1();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->bind_directives.empty());
}

TEST(CompilationUnitStructure, ConfigWithEndLabel) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig : cfg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(CompilationUnitStructure, PrimitiveWithEndLabel) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(CompilationUnitStructure, MissingEndconfigIsError) {
  EXPECT_FALSE(ParseOk(
      "module m; endmodule\n"
      "config c;\n"
      "  design m;"));
}

TEST(CompilationUnitStructure, MissingEndprimitiveIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"));
}

}  // namespace
