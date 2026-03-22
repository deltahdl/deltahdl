#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewSimulation, NewAllocatesWithSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayNewSimulation, NewDefaultInitializesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewZeroSizeCreatesEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[0];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, NewWithInitTruncates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30, 40};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPads) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPreservesOnPad) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizeNewSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizePadZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

}  // namespace
