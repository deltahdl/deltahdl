#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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
     ForwardDefinedCompilationUnitFunctionIsGathered) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer x;\n"
      "  initial x = later_add(2, 3);\n"
      "endmodule\n"
      "function int later_add(int a, int b);\n"
      "  return a + b;\n"
      "endfunction\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(CuListHas(design, "later_add"));
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
  EXPECT_TRUE(CuListHas(design, "f"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     ABareEnableFindsAnEnclosingModulesTask) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf; initial t; endmodule\n"
      "module a; leaf l (); endmodule\n"
      "module b; leaf l (); endmodule\n"
      "module top; task t; endtask a ia (); b ib (); endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskAndFunctionNameResolutionElaboration,
     ACallNamingNothingAnywhereIsUndeclared) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf; initial nosuch(); endmodule\n"
      "module top; task t; endtask leaf l (); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier 'nosuch'", 1, "23.9"));
}

}  // namespace
