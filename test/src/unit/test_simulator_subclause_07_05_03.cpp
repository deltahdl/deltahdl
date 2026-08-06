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

// The emptying rule is element-type independent: a dynamic array of a wider
// vector type is cleared to zero size just like an int array.
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

// Input form: array sized/populated by the new[N](src) copy constructor
// (§7.5.1) is still emptied to zero size by delete().
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

// "empties the array" observed through element contents, not just the size
// counter: after delete a previously populated element reads back as the
// default value of a nonexistent entry (Table 7-1).
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

// Element-type coverage: dynamic arrays admit every variable data type as an
// element (§7.5), and delete() empties the array regardless. A real-element
// array exercises the real-valued storage path.
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

// Element-type coverage: string elements use a distinct storage path from
// packed vectors; delete() still empties the array to zero size.
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

// Element-type coverage: a 4-state (logic) vector element type, distinct from
// the 2-state bit-vector path, is likewise emptied to zero size.
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

// Element-type coverage: the element type may itself be an array (§7.5). The
// outer dynamic array, sized via new[] (§7.5.1), is emptied to zero size.
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
