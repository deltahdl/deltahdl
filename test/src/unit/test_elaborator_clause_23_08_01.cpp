#include "fixture_elaborator.h"

namespace {

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
     CuScopeFunctionCalledByBareNameFromModule) {
  EXPECT_TRUE(
      ElabOk("function int cu_add(int a, int b);\n"
             "  return a + b;\n"
             "endfunction\n"
             "module m;\n"
             "  integer x;\n"
             "  initial x = cu_add(2, 3);\n"
             "endmodule\n"));
}

TEST(TaskAndFunctionNameResolutionElaboration,
     CuScopeTaskCalledByBareNameFromModule) {
  EXPECT_TRUE(
      ElabOk("task cu_tick;\n"
             "endtask\n"
             "module m;\n"
             "  initial cu_tick();\n"
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

}  // namespace
