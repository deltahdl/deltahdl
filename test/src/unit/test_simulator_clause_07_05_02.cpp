#include "builders_ast.h"
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

// §7.5.2: a dynamic array explicitly created with a zero-length new[] is empty,
// so its current size is reported as zero. This is the created-array branch at
// the empty boundary, distinct from a never-created array.
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

// §7.5.2 prototype "function int size();": the returned value is an int, i.e. a
// 32-bit quantity, independent of the array's element width or current length.
TEST(DynamicArraySizeSimulation, SizeReturnsIntWidth) {
  SimFixture f;
  MakeDynArray(f, "d", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "d", "size", {});
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 32u);
}

// §7.5.2: the size method is equivalent to the $size(addr, 1) array query
// system function. For a created array both yield the same element count.
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

// §7.5.2: the equivalence with $size(addr, 1) holds for an uncreated array as
// well; both report zero.
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
