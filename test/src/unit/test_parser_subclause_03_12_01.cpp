#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Parses `src` and asserts it yields a valid, error-free compilation unit whose
// design-element collections are all empty. Returns the parse result so callers
// can make additional assertions (e.g. on classes or cu_items).
static ParseResult ParseEmptyCompilationUnit(const char* src) {
  auto r = Parse(src);
  EXPECT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  if (r.cu != nullptr) {
    EXPECT_TRUE(r.cu->modules.empty());
    EXPECT_TRUE(r.cu->programs.empty());
    EXPECT_TRUE(r.cu->interfaces.empty());
    EXPECT_TRUE(r.cu->checkers.empty());
    EXPECT_TRUE(r.cu->packages.empty());
    EXPECT_TRUE(r.cu->udps.empty());
    EXPECT_TRUE(r.cu->configs.empty());
  }
  return r;
}

TEST(CompilationUnitParsing, CuScopeTaskParsed) {
  auto r = Parse("task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

TEST(CompilationUnitParsing, ForwardRefSyntaxValid) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

TEST(CompilationUnitParsing, PackageAndModule) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}
TEST(CompilationUnitParsing, TopLevelFunction) {
  auto r = Parse(
      "function int my_func(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "class C;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(CompilationUnitParsing, CuScopeTypedef) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(r.cu->cu_items[0]->name, "myint");
}

TEST(CompilationUnitParsing, CuScopeLocalparam) {
  auto r = Parse(
      "localparam int WIDTH = 8;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "WIDTH");
}

TEST(CompilationUnitParsing, CuScopeParameter) {
  auto r = Parse(
      "parameter int DEPTH = 16;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "DEPTH");
}

TEST(CompilationUnitParsing, CuScopeImport) {
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

TEST(CompilationUnitParsing, CuScopeDataDecl) {
  auto r = Parse(
      "bit b;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "b");
}

TEST(CompilationUnitParsing, CuScopeNamedEventDeclaration) {
  auto r = Parse(
      "event e;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "e");
}

TEST(CompilationUnitParsing, DollarUnitScopeResolutionExpr) {
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

TEST(CompilationUnitParsing, DollarUnitScopeInAssignment) {
  EXPECT_TRUE(
      ParseOk("task t;\n"
              "  int b;\n"
              "  b = 5 + $unit::b;\n"
              "endtask\n"
              "module m; endmodule\n"));
}

TEST(CompilationUnitParsing, MultipleCuScopeItems) {
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

TEST(CompilationUnitStructure, EmptySourceProducesValidCompilationUnit) {
  auto r = ParseEmptyCompilationUnit("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes.empty());
  EXPECT_TRUE(r.cu->cu_items.empty());
}

TEST(CompilationUnitStructure,
     WhitespaceOnlySourceProducesValidCompilationUnit) {
  ParseEmptyCompilationUnit("   \t\n\n  \t  ");
}

TEST(CompilationUnitStructure,
     LineCommentOnlySourceProducesValidCompilationUnit) {
  ParseEmptyCompilationUnit("// this file is intentionally empty\n");
}

TEST(CompilationUnitStructure,
     BlockCommentOnlySourceProducesValidCompilationUnit) {
  ParseEmptyCompilationUnit("/* nothing here */");
}

TEST(CompilationUnitStructure,
     MixedWhitespaceAndCommentsProducesValidCompilationUnit) {
  ParseEmptyCompilationUnit(
      "\n"
      "  // line comment\n"
      "\t/* block comment */\n"
      "  /* multi-line\n"
      "     block comment */\n"
      "\n");
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

TEST(CompilationUnitParsing, CompilationUnitScopeCannotBeImportedWildcard) {
  EXPECT_FALSE(
      ParseOk("import $unit::*;\n"
              "module m; endmodule\n"));
}

TEST(CompilationUnitParsing, CompilationUnitScopeCannotBeImportedSelective) {
  EXPECT_FALSE(
      ParseOk("import $unit::foo;\n"
              "module m; endmodule\n"));
}

TEST(CompilationUnitParsing, CuScopeSelectiveImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "import pkg::myint;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(CompilationUnitParsing, OnlyCuScopeItemsNoDesignElements) {
  auto r = Parse(
      "typedef int myint;\n"
      "function int helper(int x); return x; endfunction\n"
      "task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  ASSERT_EQ(r.cu->cu_items.size(), 3u);
}

TEST(CompilationUnitParsing, DollarUnitInSubexpression) {
  auto r = Parse(
      "int x;\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::x + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CompilationUnitParsing, BareStatementAtTopLevelIsError) {
  EXPECT_FALSE(ParseOk("assign x = 1;"));
}

TEST(CompilationUnitStructure, AllDescriptionTypesCoexist) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "class C; endclass\n"
      "checker chk; endchecker\n"
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 0 ; 1 : 1 ; endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design work.m;\n"
      "  default liblist work;\n"
      "endconfig\n"
      "bind m chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(CompilationUnitParsing, DesignElementsInterleaveWithNonDesignElements) {
  auto r = Parse(
      "typedef int myint;\n"
      "module m; endmodule\n"
      "class C; int x; endclass\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

}  // namespace
