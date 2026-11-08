#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteAfterNew) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[8];\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteOnEmptyArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, ReallocateAfterDelete) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    d = new[4];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesWideVectorArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] d[] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteAfterCopyConstructorNew) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{1, 2, 3};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3](src);\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteClearsElementContents) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesRealArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  real d[] = '{1.5, 2.5, 3.5};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesStringArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  string d[] = '{\"a\", \"bb\", \"ccc\"};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesFourStateArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] d[] = '{8'h11, 8'h22, 8'h33};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayDeleteSimulation, DeleteEmptiesArrayOfArrays) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[][];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

}  // namespace
