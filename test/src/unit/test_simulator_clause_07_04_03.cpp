#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §7.4.3: Write to memory word and read back by variable address.
TEST(MemorySimulation, WordWriteAndReadByAddress) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "  int result;\n"
      "  int addr;\n"
      "  initial begin\n"
      "    mema[5] = 8'hA5;\n"
      "    addr = 5;\n"
      "    result = mema[addr];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

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
