#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopSyntaxSimulation, ForCompoundAssignStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 10; i += 2)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, ForPreDecrementStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] last;\n"
      "  initial begin\n"
      "    last = 8'd0;\n"
      "    for (int i = 5; i > 0; --i)\n"
      "      last = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "last");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopSyntaxSimulation, ForPreIncrementStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 5; ++i)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, RepeatLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    repeat (3) total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopSyntaxSimulation, WhileLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    while (x < 5) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, DoWhileRunsAtLeastOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    do x = x + 8'd1; while (x < 5);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(LoopSyntaxSimulation, ForeverWithBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd7) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopSyntaxSimulation, ForeachIteratesEachElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] count;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    foreach (arr[i]) count = count + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopSyntaxSimulation, ForMultipleInitsAndSteps) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] j;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (i = 0, j = 10; i < j; i = i + 1, j = j - 1)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, ForVariableOfATypeReference) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  int x, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    for (var type(x) i = -2; i < 1; i++) s += i;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFDu);
}

TEST(LoopSyntaxSimulation, AForeachArrayNamedThroughAPrefixIsIterated) {
  SimFixture f;
  auto out = RunCapture(
      "class C;\n"
      "  static int tab[2] = '{4, 5};\n"
      "  int arr[3] = '{1, 2, 3};\n"
      "  function void f;\n"
      "    int n = 0;\n"
      "    foreach (this.arr[i]) n += this.arr[i];\n"
      "    $display(\"t %0d\", n);\n"
      "  endfunction\n"
      "endclass\n"
      "package pkg;\n"
      "  int mem[4];\n"
      "endpackage\n"
      "module u;\n"
      "  int arr[3];\n"
      "endmodule\n"
      "module m;\n"
      "  u u();\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    automatic int n = 0;\n"
      "    c.f();\n"
      "    foreach (C::tab[i]) n += C::tab[i];\n"
      "    $display(\"c %0d\", n);\n"
      "    n = 0;\n"
      "    foreach (pkg::mem[i]) n++;\n"
      "    $display(\"p %0d\", n);\n"
      "    foreach (u.arr[i]) u.arr[i] = i + 7;\n"
      "    $display(\"h %0d %0d\", u.arr[0], u.arr[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t 6\nc 9\np 4\nh 7 9\n");
}

TEST(LoopSyntaxSimulation, DISABLED_AForeachOverASuperArrayIteratesTheBase) {
  SimFixture f;
  auto out = RunCapture(
      "class B;\n"
      "  int arr[3] = '{1, 2, 3};\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void f;\n"
      "    int n = 0;\n"
      "    foreach (super.arr[i]) n++;\n"
      "    super.arr[1] = 6;\n"
      "    $display(\"s %0d %0d\", n, arr[1]);\n"
      "    n = 0;\n"
      "    foreach (this.super.arr[i]) n++;\n"
      "    $display(\"ts %0d\", n);\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic D d = new;\n"
      "    d.f();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s 3 6\nts 3\n");
}

TEST(LoopSyntaxSimulation, DISABLED_AForeachOverAUnitScopedArrayIsIterated) {
  SimFixture f;
  auto out = RunCapture(
      "int um[5];\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int n = 0;\n"
      "    foreach ($unit::um[i]) n++;\n"
      "    $display(\"u %0d\", n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "u 5\n");
}

}  // namespace
