#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedArraySimulation, MultiDimPackedArrayAsSingleVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    result = x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABCDu);
}

TEST(PackedArraySimulation, MultiDimPackedArrayPartSelect) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    x = 16'hABCD;\n"
      "    result = x[15:8];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedArraySimulation, PackedArrayBitSelect) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    x = 8'b10100101;\n"
      "    result = x[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}
