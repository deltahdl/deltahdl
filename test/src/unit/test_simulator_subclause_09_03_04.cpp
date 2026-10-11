#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

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

// §9.3.4: a named block is a scope of the hierarchy, and a variable it
// declares is read from another process by the block's name, through the
// module's, and through a task for a block nested in the task.
TEST(BlockNameSimulation, NamedBlockVariableReadByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  initial begin : b1\n"
                 "    static int cnt = 7;\n"
                 "    #10 cnt = 8;\n"
                 "    #10;\n"
                 "  end\n"
                 "  task tk; begin : inner static int w = 5; #8; end endtask\n"
                 "  initial tk();\n"
                 "  initial begin\n"
                 "    #5 $display(\"%0d %0d\", b1.cnt, t.b1.cnt);\n"
                 "    #1 $display(\"%0d\", tk.inner.w);\n"
                 "    #6 $display(\"%0d\", b1.cnt);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "7 7\n"
      "5\n"
      "8\n");
}

// §9.3.4 with §6.21: a block declaring an item is a scope of its own, so a
// nested block's `x` is a variable apart from the enclosing block's, which it
// hides, and its initializer is applied to it; the outer `x` keeps its 5.
TEST(BlockNameSimulation, ANestedBlockDeclarationHidesTheOuterVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; initial begin\n"
                       "  int x; x = 5;\n"
                       "  begin int x = 7; $display(\"%0d\", x); x = 9; end\n"
                       "  begin int x; x = 3; end\n"
                       "  $display(\"%0d\", x);\n"
                       "end endmodule\n",
                       f),
            "7\n5\n");
}

}  // namespace
