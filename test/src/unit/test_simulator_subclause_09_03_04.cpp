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

TEST(BlockNameSimulation, ANestedBlockDeclarationHidesTheOuterVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t; initial begin\n"
          "  int x; x = 5;\n"
          "  begin automatic int x = 7; $display(\"%0d\", x); x = 9; end\n"
          "  begin int x; x = 3; end\n"
          "  $display(\"%0d\", x);\n"
          "end endmodule\n",
          f),
      "7\n5\n");
}

TEST(BlockNameSimulation, ParametersOfANamedBlockReadByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin : b1\n"
                       "    parameter int P = 6;\n"
                       "    localparam int L = 9;\n"
                       "    #10;\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d %0d\", b1.P, b1.L);\n"
                       "endmodule\n",
                       f),
            "6 9\n");
}

TEST(BlockNameSimulation, NamedEventOfANamedBlockTriggeredByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin : b1\n"
                       "    event ev;\n"
                       "    #20;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    @(b1.ev);\n"
                       "    $display(\"woke %0t\", $time);\n"
                       "  end\n"
                       "  initial #7 -> b1.ev;\n"
                       "endmodule\n",
                       f),
            "woke 7\n");
}

TEST(BlockNameSimulation, NamedForkVariableReadAndWrittenByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial fork : f1\n"
                       "    static int x = 4;\n"
                       "    #10 $display(\"in %0d\", x);\n"
                       "  join\n"
                       "  initial begin\n"
                       "    #2 $display(\"%0d\", f1.x);\n"
                       "    f1.x = 11;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4\nin 11\n");
}

TEST(BlockNameSimulation,
     LabelledBlockVariableReadAndWrittenByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial lbl: begin\n"
                       "    static int x = 3;\n"
                       "    #10 $display(\"in %0d\", x);\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 $display(\"%0d\", lbl.x);\n"
                       "    t.lbl.x = 8;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3\nin 8\n");
}

}  // namespace
