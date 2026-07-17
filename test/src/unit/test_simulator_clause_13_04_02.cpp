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

// §13.4.2: a function with no explicit lifetime, defined within a module that
// is declared automatic, is implicitly automatic. It is therefore reentrant,
// so this recursive function computes 5! correctly; a static function would
// clobber its operand across the nested calls.
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

// §13.4.2: a function with no explicit lifetime, in an ordinary (non-automatic)
// module, defaults to static — its items are statically allocated and shared
// across successive calls. The implicit return variable therefore accumulates,
// so the second call sees the first call's result (5 + 3 = 8). A reentrant
// allocation would reset it and yield 3.
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

// §13.4.2: a local declared static inside an automatic function overrides the
// function's lifetime for that variable, so it is allocated once and retains
// its value across calls. acc accumulates 5 then 3, so the second call returns
// 8; if the static override were ignored the per-call value would be 3.
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

// §13.4.2: the mirror override — a local declared automatic inside a static
// function is reallocated (and re-initialized) on every call rather than
// sharing the function's static storage. acc restarts at 0 each call, so the
// second call returns 3, not the 8 a static local would accumulate. This is the
// "automatic within a static function" half of the override rule.
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

// §13.4.2: a function with no explicit lifetime, defined in an ordinary
// package, defaults to static -- the package input form of the default-static
// rule (the clause names module, interface, program, and package). Its plain
// local cnt is statically allocated and shared across calls made from the
// importing module, so the second call sees the first call's accumulated value
// (5 + 3 = 8). This exercises the dedicated package lifetime-defaulting path,
// distinct from the module form (DefaultLifetimeFunctionRetainsStaticStorage).
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

// §13.4.2: a function with no explicit lifetime defined in a package marked
// automatic is implicitly automatic (the package input form of the implicit-
// automatic rule). Its local is reallocated each call, so cnt restarts and the
// second call returns 3. Contrast DefaultFunctionInPackageIsStatic above.
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

}  // namespace
