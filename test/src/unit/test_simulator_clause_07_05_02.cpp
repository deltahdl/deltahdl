#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArraySizeSimulation, UncreatedReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArraySizeSimulation, ReturnsCurrentSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[7];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(DynamicArraySizeSimulation, ReflectsInitializerListSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40, 50};\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(DynamicArraySizeSimulation, ReflectsResize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[10];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(DynamicArraySizeSimulation, SizeUsedInExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3, 4};\n"
      "  int result;\n"
      "  initial result = d.size() + 100;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 104u);
}

TEST(DynamicArraySizeSimulation, SizeAfterDeleteIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d.delete();\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

}  // namespace
