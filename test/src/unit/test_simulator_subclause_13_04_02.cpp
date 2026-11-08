#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeSim, RecursiveAutomaticFunction) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int factorial(input int n);\n"
      "    if (n <= 1)\n"
      "      factorial = 1;\n"
      "    else\n"
      "      factorial = factorial(n - 1) * n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = factorial(5);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 120u);
}

TEST(FunctionLifetimeSim, DefaultFunctionInAutomaticModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int factorial(input int n);\n"
      "    if (n <= 1)\n"
      "      factorial = 1;\n"
      "    else\n"
      "      factorial = factorial(n - 1) * n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = factorial(5);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 120u);
}

TEST(FunctionLifetimeSim, DefaultLifetimeFunctionRetainsStaticStorage) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  function int accum(input int v);\n"
      "    accum = accum + v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = accum(5);\n"
      "    r2 = accum(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 8u);
}

TEST(FunctionLifetimeSim, StaticLocalInAutomaticFunctionRetainsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  function automatic int tally(input int v);\n"
      "    static int acc = 0;\n"
      "    acc = acc + v;\n"
      "    return acc;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = tally(5);\n"
      "    r2 = tally(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 8u);
}

TEST(FunctionLifetimeSim, AutomaticLocalInStaticFunctionIsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  function static int tally(input int v);\n"
      "    automatic int acc = 0;\n"
      "    acc = acc + v;\n"
      "    return acc;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r1 = tally(5);\n"
      "    r2 = tally(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionLifetimeSim, DefaultFunctionInPackageIsStatic) {
  auto val = RunAndGet(
      "package pk;\n"
      "  function int accum(input int v);\n"
      "    int cnt;\n"
      "    cnt = cnt + v;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  initial begin\n"
      "    r1 = accum(5);\n"
      "    r2 = accum(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 8u);
}

TEST(FunctionLifetimeSim, DefaultFunctionInAutomaticPackageIsAutomatic) {
  auto val = RunAndGet(
      "package automatic pk;\n"
      "  function int accum(input int v);\n"
      "    int cnt;\n"
      "    cnt = cnt + v;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  logic [31:0] r1;\n"
      "  logic [31:0] r2;\n"
      "  initial begin\n"
      "    r1 = accum(5);\n"
      "    r2 = accum(3);\n"
      "  end\n"
      "endmodule\n",
      "r2");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionLifetimeSim, ClassMethodRecursesThroughThisAndBareName) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    function int fib(int n);\n"
      "      return n < 2 ? n : fib(n - 1) + this.fib(n - 2);\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    static C h = new;\n"
      "    result = h.fib(10);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 55u);
}

TEST(FunctionLifetimeSim, ClassMethodRecursesThroughThisAlone) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    function int fact(int n);\n"
      "      if (n <= 1) return 1;\n"
      "      return this.fact(n - 1) * n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    static C h = new;\n"
      "    result = h.fact(5);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 120u);
}

TEST(FunctionLifetimeSim, ThisQualifiedCallStatementWritesOwnProperty) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int count;\n"
      "    function void bump();\n"
      "      count = count + 1;\n"
      "    endfunction\n"
      "    function void twice();\n"
      "      this.bump();\n"
      "      this.bump();\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    static C h = new;\n"
      "    h.twice();\n"
      "    result = h.count;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(FunctionLifetimeSim, StaticFunctionQueueLocalKeptBetweenCalls) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int grow();\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    return q.size();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    void'(grow());\n"
      "    result = grow();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(FunctionLifetimeSim, StaticFunctionAssociativeLocalKeptBetweenCalls) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int note(int k);\n"
      "    int m[int];\n"
      "    m[k] = 1;\n"
      "    return m.num();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    void'(note(1));\n"
      "    result = note(2);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(FunctionLifetimeSim, StaticFunctionFixedArrayLocalKeptBetweenCalls) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int count();\n"
      "    int a[2];\n"
      "    a[0]++;\n"
      "    return a[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    void'(count());\n"
      "    void'(count());\n"
      "    result = count();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionLifetimeSim, AutomaticFunctionQueueLocalFreshEachCall) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function automatic int grow();\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    return q.size();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    void'(grow());\n"
      "    result = grow();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(FunctionLifetimeSim, PackageFunctionQueueLocalKeptBetweenCalls) {
  auto val = RunAndGet(
      "package p;\n"
      "  function int grow();\n"
      "    int q[$];\n"
      "    q.push_back(7);\n"
      "    return q.size();\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    void'(p::grow());\n"
      "    result = p::grow();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(FunctionLifetimeSim, PackageFunctionStaticLocalSharedByEveryInstance) {
  auto val = RunAndGet(
      "package p;\n"
      "  function int count(); static int n = 0; n++; return n; endfunction\n"
      "endpackage\n"
      "module c; int r; initial r = p::count(); endmodule\n"
      "module t;\n"
      "  c u1();\n"
      "  c u2();\n"
      "  int r;\n"
      "  initial #1 r = p::count();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(FunctionLifetimeSim, UnitFunctionStaticLocalSharedByEveryInstance) {
  auto val = RunAndGet(
      "function int count();\n"
      "  begin : b static int n = 0; n++; return n; end\n"
      "endfunction\n"
      "module c; int r; initial r = count(); endmodule\n"
      "module t;\n"
      "  c u1();\n"
      "  c u2();\n"
      "  int r;\n"
      "  initial #1 r = count();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

}  // namespace
