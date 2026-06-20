#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.8.1 inserts a lookup in the complete compilation unit between step a) and
// step b) of the upward hierarchical resolution. The elaborator implements that
// by gathering the unit-scope tasks and functions of the reference into a
// dedicated list, distinct from any module's local subroutines, so a bare name
// can later resolve to them from any point in the hierarchy.
bool CuListHas(const RtlirDesign* design, std::string_view name) {
  for (const auto* item : design->cu_function_decls) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        item->name == name) {
      return true;
    }
  }
  return false;
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CompilationUnitFunctionIsGatheredForResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "function int cu_add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n"
      "module m;\n"
      "  integer x;\n"
      "  initial x = cu_add(2, 3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(CuListHas(design, "cu_add"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CompilationUnitTaskIsGatheredForResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "task cu_tick;\n"
      "endtask\n"
      "module m;\n"
      "  initial cu_tick();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(CuListHas(design, "cu_tick"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     ModuleLocalFunctionIsNotPlacedInCompilationUnitList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int local_f(int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  integer x;\n"
      "  initial x = local_f(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  // A module-local subroutine is found in step a) and never belongs to the
  // compilation-unit lookup, so it must not appear in that list.
  EXPECT_FALSE(CuListHas(design, "local_f"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     TaskLookupSearchesEnclosingModulesNotInstances) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  initial t();\n"
             "endmodule\n"
             "module parent;\n"
             "  task t;\n"
             "  endtask\n"
             "  leaf l1();\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     FunctionLookupSearchesEnclosingModulesNotInstances) {
  EXPECT_TRUE(
      ElabOk("module leaf;\n"
             "  integer x;\n"
             "  initial x = f(1);\n"
             "endmodule\n"
             "module parent;\n"
             "  function int f(int y);\n"
             "    return y + 1;\n"
             "  endfunction\n"
             "  leaf l1();\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     TaskBodyCallsCompilationUnitFunction) {
  EXPECT_TRUE(
      ElabOk("function int f(int y);\n"
             "  return y + 1;\n"
             "endfunction\n"
             "module m;\n"
             "  task t;\n"
             "    int x;\n"
             "    x = f(1);\n"
             "  endtask\n"
             "  initial t();\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CuScopeFunctionCalledFromGrandchildModule) {
  EXPECT_TRUE(
      ElabOk("function int cu_id(int a);\n"
             "  return a;\n"
             "endfunction\n"
             "module leaf;\n"
             "  integer x;\n"
             "  initial x = cu_id(7);\n"
             "endmodule\n"
             "module mid;\n"
             "  leaf l1();\n"
             "endmodule\n"
             "module top;\n"
             "  mid m1();\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     ModuleLocalFunctionShadowsCompilationUnitFunction) {
  EXPECT_TRUE(
      ElabOk("function int f(int a);\n"
             "  return a + 100;\n"
             "endfunction\n"
             "module m;\n"
             "  function int f(int a);\n"
             "    return a;\n"
             "  endfunction\n"
             "  integer x;\n"
             "  initial x = f(1);\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CompilationUnitFunctionCalledFromNamedBlock) {
  EXPECT_TRUE(
      ElabOk("function int cu_f(int a);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "  integer x;\n"
             "  initial begin : blk\n"
             "    x = cu_f(9);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CompilationUnitListHoldsUnitFunctionDespiteModuleRedeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "function int f(int a);\n"
      "  return a + 100;\n"
      "endfunction\n"
      "module m;\n"
      "  function int f(int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  integer x;\n"
      "  initial x = f(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  // The compilation-unit lookup is sourced only from the enclosing unit's
  // items, so the unit-scope 'f' stays in the list even though a module
  // declares its own 'f' under the same name.
  EXPECT_TRUE(CuListHas(design, "f"));
}

}  // namespace
