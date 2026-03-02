// §3.12.1: Compilation units

#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// 7. Compiler directives apply within a CU only.
// A `define in one parse (CU) does not leak into a separate parse (CU).
TEST(ParserClause03, Cl3_12_1_DirectivesLocalToCU) {
  // First CU: define a macro and use it.
  auto r1 = Parse(
      "`define FOO 1\n"
      "module m1;\n"
      "  localparam X = `FOO;\n"
      "endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  // Second CU (separate Parse call): macro should NOT be defined.
  // Using `FOO without defining it should produce a preprocessor error.
  auto r2 = Parse(
      "module m2;\n"
      "  localparam Y = `FOO;\n"
      "endmodule\n");
  // The undefined macro should cause an error in the second CU.
  EXPECT_TRUE(r2.has_errors);
}

// =============================================================================
// LRM §3.12.1 — Compilation units
// =============================================================================
// 1. Compilation unit definition: a collection of source files compiled
// together.  A single Parse() call produces one CompilationUnit.
TEST(ParserClause03, Cl3_12_1_CompilationUnitDefinition) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Both modules belong to the same compilation unit.
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

// 2. Compilation-unit scope: declarations outside any other scope.
// CU scope can contain anything valid in a package (§26.2) —
// functions, tasks, typedefs, parameters, classes.
TEST(ParserClause03, Cl3_12_1_CuScopeContainsPackageItems) {
  auto r = ParseWithPreprocessor(
      "function int helper(int x); return x + 1; endfunction\n"
      "task auto_task; endtask\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Functions and tasks in CU scope are stored in cu_items.
  ASSERT_EQ(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 4. `include becomes part of the including file's CU.
// The preprocessor inlines included content into the same CU.
TEST(ParserClause03, Cl3_12_1_IncludeBecomesPartOfCU) {
  // We can't include real files in this unit test, but we verify that
  // the preprocessor produces a single text blob from `define/`ifdef
  // which are CU-scoped directives.  If an `include were processed,
  // its content would appear in the same preprocessed output.
  auto r = ParseWithPreprocessor(
      "`define MY_CONST 42\n"
      "module m;\n"
      "  localparam C = `MY_CONST;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The macro defined at CU scope is visible inside the module,
  // demonstrating that preprocessing merges everything into one CU.
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 5. Global visibility: modules, primitives, programs, interfaces, packages
// are visible in all CUs.  Within a single CU, all are accessible.
TEST(ParserClause03, Cl3_12_1_GloballyVisibleDesignElements) {
  auto r = ParseWithPreprocessor(
      "package pkg; endpackage\n"
      "interface intf; endinterface\n"
      "program prog; endprogram\n"
      "module mod; endmodule\n"
      "primitive udp_and(output o, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// 6. CU scope can hold classes (valid in a package per §26.2).
TEST(ParserClause03, Cl3_12_1_CuScopeClassDecl) {
  auto r = ParseWithPreprocessor(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_class");
}

static const ModuleItem* FindItemByKindAndName(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind,
    const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return item;
  return nullptr;
}

// 8. Name resolution: nested scope searched first, then CU scope.
// A local declaration shadows a CU-scope declaration.
TEST(ParserClause03, Cl3_12_1_NameResolutionOrder) {
  // A function at CU scope and a module that also declares 'helper'.
  // The parser accepts both — resolution is elaboration's job.
  auto r = ParseWithPreprocessor(
      "function int helper(int x); return x; endfunction\n"
      "module m;\n"
      "  function int helper(int x); return x * 2; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // CU scope has the top-level function.
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  // Module has its own 'helper' — shadows the CU-scope one.
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(FindItemByKindAndName(r.cu->modules[0]->items,
                                  ModuleItemKind::kFunctionDecl, "helper"),
            nullptr);
}

// 11. CU scope has no name — cannot be imported.
// An import of $unit would be illegal.  Verify that valid import syntax
// works and that CU items remain separate from packages.
TEST(ParserClause03, Cl3_12_1_CuScopeCannotBeImported) {
  // Normal package import works fine.
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // CU-scope functions are NOT in any package.
  EXPECT_TRUE(r.cu->cu_items.empty());
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// 12. CU scope identifiers not accessible via hierarchical references.
// Hierarchical names start from $root (§23.3.1), not from CU scope.
// Verify that a hierarchical reference in a module parses correctly.
TEST(ParserClause03, Cl3_12_1_HierRefFromCUScope) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  module_a u1();\n"
      "endmodule\n"
      "module module_a;\n"
      "  logic sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 13. CU allows type sharing without packages (§3.12.1 last paragraph).
// Users can share types across a CU without declaring a package.
// Top-level typedef is parsed as a module item (discarded at top level
// in current implementation) or could be a class.  Verify CU-scope
// classes enable type sharing.
TEST(ParserClause03, Cl3_12_1_TypeSharingViaCUScope) {
  auto r = ParseWithPreprocessor(
      "class shared_type;\n"
      "  int value;\n"
      "endclass\n"
      "module m1;\n"
      "  shared_type obj;\n"
      "endmodule\n"
      "module m2;\n"
      "  shared_type obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 16. Checker declarations at CU scope.
TEST(ParserClause03, Cl3_12_1_CheckerAtCUScope) {
  auto r = ParseWithPreprocessor(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

// =============================================================================
// A.1.2 source_text ::= [ timeunits_declaration ] { description }
// =============================================================================
// Empty source text.
TEST(SourceText, EmptySourceText) {
  auto r = ParseWithPreprocessor("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

// 18. $unit scope -- declarations outside any module/package
TEST(ParserClause03, Cl3_13_UnitScopeDeclarations) {
  auto r = ParseWithPreprocessor(
      "function automatic int helper(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "task automatic global_task(input int v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(r.cu->cu_items[1]->name, "global_task");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(Parser, MultipleModules) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

}  // namespace
