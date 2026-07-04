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

// A named parallel block (par_block from §9.3.2) closed with a matching join
// label runs end-to-end: the block name is accepted and all forked children
// complete before control passes the join, so their combined effect is visible.
TEST(BlockNameSimulation, NamedForkBlockSimulates) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    fork : workers\n"
      "      a = 30;\n"
      "      b = 12;\n"
      "    join : workers\n"
      "    result = a + b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
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
