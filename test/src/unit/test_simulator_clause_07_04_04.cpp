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

TEST(MultidimensionalArraySimulation, DistinctUnpackedElementsAreIndependent) {
  // §7.4.4: each unpacked index selects a separate element. Writing two
  // different elements and combining them in one expression shows they hold
  // independent storage rather than aliasing.
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'h11111111;\n"
      "    joe[2] = 32'h22222222;\n"
      "    result = joe[2] - joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x11111111u);
}

TEST(MultidimensionalArraySimulation, PackedElementParticipatesInArithmetic) {
  // §7.4.4: an element of a multidimensional array is a single packed word
  // (here 32 bits from [3:0][7:0]) and takes part in arithmetic as one value,
  // mirroring the standard's whole-element add of one array slot into another.
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[8] = 32'h0000000F;\n"
      "    joe[9] = joe[8] + 1;\n"
      "    result = joe[9];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

}  // namespace
