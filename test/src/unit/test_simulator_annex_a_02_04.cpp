#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DeclarationAssignmentSim, VarDeclInitializerAppliesAtRuntime) {
  auto v = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  int result;\n"
      "  initial result = x;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(DeclarationAssignmentSim, VarDeclDynamicArrayNewSizeInitializer) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DeclarationAssignmentSim, VarDeclDynamicArrayReductionOverBraceInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{4, 5, 6};\n"
      "  int result;\n"
      "  initial result = d.sum() with (item);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 15u);
}

TEST(DeclarationAssignmentSim, VarDeclDynamicArrayNewCopyInitializer) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{7, 8};\n"
      "  int d[] = new[3](src);\n"
      "  int result;\n"
      "  initial result = d.size() * 100 + d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 308u);
}

TEST(DeclarationAssignmentSim, VarDeclClassNewInitializerConstructsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(); v = 42; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    result = c.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(DeclarationAssignmentSim, VarDeclClassNewWithArgsInitializer) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int a); v = a * 2; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new(21);\n"
      "    result = c.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
