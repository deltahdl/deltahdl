#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

constexpr const char* kCountingFunction =
    "(); int c; c++; return c; endfunction\n";

std::string CountingFunction(const char* head) {
  return std::string("  ") + head + kCountingFunction;
}

TEST(FunctionLifetimeSim,
     AnInterfaceFunctionIsStaticUnlessTheInterfaceIsAutomatic) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i;\n" + CountingFunction("function int f") +
                           "endinterface\n"
                           "interface automatic ia;\n" +
                           CountingFunction("function int fa") +
                           CountingFunction("function static int fs") +
                           "endinterface\n"
                           "module m;\n"
                           "  i u(); ia v();\n"
                           "  int a, b, c, d, e, g;\n"
                           "  initial begin\n"
                           "    a = u.f(); b = u.f(); c = v.fa(); d = v.fa();\n"
                           "    e = v.fs(); g = v.fs();\n"
                           "    $display(\"%0d %0d %0d %0d %0d %0d\", a, b, c, "
                           "d, e, g);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1 2 1 1 1 2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionLifetimeSim, AProgramFunctionIsStaticUnlessTheProgramIsAutomatic) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n" + CountingFunction("function int f") +
                           "  int a, b;\n"
                           "  initial begin\n"
                           "    #1 a = f(); b = f();\n"
                           "    $display(\"%0d %0d\", a, b);\n"
                           "  end\n"
                           "endprogram\n"
                           "program automatic q;\n" +
                           CountingFunction("function int fa") +
                           CountingFunction("function static int fs") +
                           "  int a, b, e, g;\n"
                           "  initial begin\n"
                           "    #2 a = fa(); b = fa(); e = fs(); g = fs();\n"
                           "    $display(\"%0d %0d %0d %0d\", a, b, e, g);\n"
                           "  end\n"
                           "endprogram\n",
                       f),
            "1 2\n1 1 1 2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionLifetimeSim, TheFactorialExampleDisplaysItsResults) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module tryfact;\n"
                       "  function automatic integer factorial "
                       "(input [31:0] operand);\n"
                       "    if (operand >= 2)\n"
                       "      factorial = factorial (operand - 1) * operand;\n"
                       "    else\n"
                       "      factorial = 1;\n"
                       "  endfunction: factorial\n"
                       "  integer result;\n"
                       "  initial begin\n"
                       "    for (int n = 0; n <= 7; n++) begin\n"
                       "      result = factorial(n);\n"
                       "      $display(\"%0d factorial=%0d\", n, result);\n"
                       "    end\n"
                       "  end\n"
                       "endmodule: tryfact\n",
                       f),
            "0 factorial=1\n1 factorial=1\n2 factorial=2\n3 factorial=6\n"
            "4 factorial=24\n5 factorial=120\n6 factorial=720\n"
            "7 factorial=5040\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionLifetimeSim, OnlyAStaticFunctionKeepsItsImplicitVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  function int st();\n"
                       "    st = st + 1;\n"
                       "  endfunction\n"
                       "  function automatic int au();\n"
                       "    au = au + 1;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d %0d %0d\", st(), st(), "
                       "au(), au());\n"
                       "endmodule\n",
                       f),
            "1 2 1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionLifetimeSim, AClassMethodIsAutomaticWhetherOrNotItIsStatic) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  function int f();\n"
                       "    int x;\n"
                       "    x++;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  static function int s();\n"
                       "    int y;\n"
                       "    y++;\n"
                       "    return y;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module m;\n"
                       "  C c = new;\n"
                       "  initial $display(\"%0d %0d %0d %0d\", c.f(), c.f(), "
                       "C::s(), C::s());\n"
                       "endmodule\n",
                       f),
            "1 1 1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionLifetimeSim,
     AFunctionDeclaredStaticInAnAutomaticScopeKeepsItsLocal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package automatic p;\n"
                       "  function static int k();\n"
                       "    int x;\n"
                       "    x++;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module automatic m;\n"
                       "  function static int g();\n"
                       "    int x;\n"
                       "    x++;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d %0d %0d\", g(), g(), "
                       "p::k(), p::k());\n"
                       "endmodule\n",
                       f),
            "1 2 1 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionLifetimeSim, AnAutomaticFunctionIsCalledThroughAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c;\n"
                       "  function automatic int f(int n);\n"
                       "    return n <= 1 ? 1 : n * f(n - 1);\n"
                       "  endfunction\n"
                       "endmodule\n"
                       "interface i;\n"
                       "  function automatic int g(int n);\n"
                       "    return n + 1;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "module m;\n"
                       "  c u();\n"
                       "  i v();\n"
                       "  initial $display(\"%0d %0d %0d\", u.f(4), v.g(1), "
                       "m.u.f(3));\n"
                       "endmodule\n",
                       f),
            "24 2 6\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionLifetimeSim, AStaticFunctionsLocalIsReadThroughAPathInEveryScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module c;\n"
                 "  function int g();\n"
                 "    int x;\n"
                 "    x = 9;\n"
                 "    return x;\n"
                 "  endfunction\n"
                 "endmodule\n"
                 "interface i;\n"
                 "  function int g();\n"
                 "    int x;\n"
                 "    x = 5;\n"
                 "    return x;\n"
                 "  endfunction\n"
                 "endinterface\n"
                 "module m;\n"
                 "  c u();\n"
                 "  i v();\n"
                 "  function int g(int a);\n"
                 "    int x;\n"
                 "    x = a * 2;\n"
                 "    return x;\n"
                 "  endfunction\n"
                 "  if (1) begin : gb\n"
                 "    function int h();\n"
                 "      int x;\n"
                 "      x = 4;\n"
                 "      return x;\n"
                 "    endfunction\n"
                 "  end\n"
                 "  int r;\n"
                 "  initial begin\n"
                 "    r = g(21) + u.g() + v.g() + gb.h();\n"
                 "    $display(\"%0d %0d %0d %0d %0d\", g.x, m.g.x, u.g.x, "
                 "v.g.x, gb.h.x);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "42 42 9 5 4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
