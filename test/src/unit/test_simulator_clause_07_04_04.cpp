#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

}
