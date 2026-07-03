#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArraySimulation, DeclWithInitHasElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial result = d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArraySimulation, DefaultUninitializedSizeZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArraySimulation, DeclWithInitCorrectSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{5, 6, 7, 8};\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

// §7.5: a dynamic array admits any variable data type as its element. Build a
// dynamic array of a packed-vector element type from real source and read an
// element back at run time to observe the non-int element type in effect.
TEST(DynamicArraySimulation, PackedVectorElementHoldsValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] d[] = '{8'hA1, 8'hB2, 8'hC3};\n"
      "  int result;\n"
      "  initial result = d[2];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xC3u);
}

}  // namespace
