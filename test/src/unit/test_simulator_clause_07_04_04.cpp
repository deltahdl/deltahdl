#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.4.4: Write and read a single element in a 2D unpacked array.
TEST(MultidimensionalArraySimulation, TwoDimElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[1][2] = 8'hAB;\n"
      "    result = mem[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

// §7.4.4: Packed dims before name combined with unpacked dims after name.
TEST(MultidimensionalArraySimulation, PackedAndUnpackedDims) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'hDEADBEEF;\n"
      "    result = joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

}  // namespace
