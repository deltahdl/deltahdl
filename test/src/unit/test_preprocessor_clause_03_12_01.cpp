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

}  // namespace
