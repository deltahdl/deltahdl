#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockNameSimulation, NamedBlockSimulates) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin : blk\n"
      "    result = 42;\n"
      "  end : blk\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
}

TEST(BlockNameSimulation, NamedBlockLocalVarSimulates) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin : blk\n"
      "    int x;\n"
      "    x = 10;\n"
      "    result = x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 10u);
}

TEST(BlockNameSimulation, NestedNamedBlocksSimulate) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin : outer\n"
      "    int a;\n"
      "    a = 5;\n"
      "    begin : inner\n"
      "      int b;\n"
      "      b = a + 3;\n"
      "      result = b;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 8u);
}

TEST(BlockNameSimulation, NamedBlockVarsAreStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    repeat (3) begin : cnt_blk\n"
      "      int x;\n"
      "      x = x + 1;\n"
      "      result = x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

}  // namespace
