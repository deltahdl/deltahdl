#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"

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

TEST(DynamicArraySizeSimulation, SizeOfEmptyCreatedArrayIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[0];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArraySizeSimulation, SizeReturnsIntWidth) {
  SimFixture f;
  MakeDynArray(f, "d", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "d", "size", {});
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 32u);
}

TEST(DynamicArraySizeSimulation, NoParenthesesPropertyForm) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d.size;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArraySizeSimulation, SizeUsedInNewSizeExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[5];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[d.size() * 4] (d);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArraySizeSimulation, ReportsElementCountForVectorElementType) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] nibble[] = new[6];\n"
      "  int result;\n"
      "  initial result = nibble.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(DynamicArraySizeSimulation, ReportsOuterDimensionOfMultidimensionalArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int m[][];\n"
      "  int result;\n"
      "  initial begin\n"
      "    m = new[3];\n"
      "    result = m.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DynamicArraySizeSimulation, EquivalentToDollarSizeDimensionOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[6];\n"
      "  int result;\n"
      "  initial result = (d.size() == $size(d, 1));\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(DynamicArraySizeSimulation, EquivalentToDollarSizeWhenUncreated) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial result = (d.size() == $size(d, 1)) && (d.size() == 0);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
