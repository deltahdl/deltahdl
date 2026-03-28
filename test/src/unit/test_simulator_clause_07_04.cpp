#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- R1+R2: packed width from dims before name, array from dims after ---

TEST(PackedAndUnpackedArraySimulation, PackedWidthAndUnpackedElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hFF;\n"
      "    arr[1] = 8'hAB;\n"
      "    result = arr[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedAndUnpackedArraySimulation, PackedWidthTruncatesOnWrite) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0] arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hFF;\n"
      "    result = arr[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xFu);
}

// --- R5: unpacked arrays from any data type ---

TEST(PackedAndUnpackedArraySimulation, UnpackedArrayOfRealType) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  real u [0:3];\n"
      "  real result;\n"
      "  initial begin\n"
      "    u[0] = 3.14;\n"
      "    u[1] = 2.72;\n"
      "    result = u[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_DOUBLE_EQ(v, 3.14);
}

}  // namespace
