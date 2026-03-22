#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.8: Write to associative array creates element dynamically, read returns it.
TEST(AssocArraySimulation, DynamicElementCreation) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.8: Multiple elements can be stored and retrieved independently.
TEST(AssocArraySimulation, MultipleElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// §7.8: Overwriting an existing key updates the element.
TEST(AssocArraySimulation, OverwriteElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 100;\n"
      "    aa[7] = 200;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

}  // namespace
