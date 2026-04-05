#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.4.3: Bit-type memory word access.
TEST(MemorySimulation, BitMemoryWordAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [7:0] mem [0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[0] = 8'hFF;\n"
      "    mem[1] = 8'h42;\n"
      "    result = mem[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x42u);
}

}  // namespace
