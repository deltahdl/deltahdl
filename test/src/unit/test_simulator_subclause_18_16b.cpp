#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(RandcaseRun, TheClausesWeightsSelectTheBranchesInProportion) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int x, i, c1 = 0, c2 = 0, c3 = 0;\n"
      "  int first_near, second_near, third_near, every;\n"
      "  initial begin\n"
      "    for (i = 0; i < 8000; i++) begin\n"
      "      x = 0;\n"
      "      randcase\n"
      "        3 : x = 1;\n"
      "        1 : x = 2;\n"
      "        4 : x = 3;\n"
      "      endcase\n"
      "      if (x == 1) c1++;\n"
      "      if (x == 2) c2++;\n"
      "      if (x == 3) c3++;\n"
      "    end\n"
      "    first_near = c1 > 2850 && c1 < 3150;\n"
      "    second_near = c2 > 850 && c2 < 1150;\n"
      "    third_near = c3 > 3850 && c3 < 4150;\n"
      "    every = c1 + c2 + c3 == 8000;\n"
      "    $display(\"%0d %0d %0d %0d\", first_near, second_near, third_near, "
      "every);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n");
}

TEST(RandcaseRun, AZeroWeightIsNotTakenAndAllZeroTakesNone) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int x, i, taken = 0, untaken, none;\n"
      "  initial begin\n"
      "    for (i = 0; i < 1000; i++) begin\n"
      "      x = 0;\n"
      "      randcase\n"
      "        3 : x = 1;\n"
      "        0 : x = 2;\n"
      "        4 : x = 3;\n"
      "      endcase\n"
      "      if (x == 2) taken++;\n"
      "    end\n"
      "    x = 0;\n"
      "    randcase\n"
      "      0 : x = 1;\n"
      "      0 : x = 2;\n"
      "    endcase\n"
      "    untaken = taken == 0;\n"
      "    none = x == 0;\n"
      "    $display(\"%0d %0d\", untaken, none);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(RandcaseRun, WeightsAreSelfDeterminedExpressionsEvaluatedOnce) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int x, i, n = 0, never = 0, wrapped = 0, calls = 0;\n"
      "  int mostly, no_second, no_wrapped;\n"
      "  byte a, b;\n"
      "  function int bump();\n"
      "    calls++;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 1; b = 1;\n"
      "    for (i = 0; i < 1000; i++) begin\n"
      "      x = 0;\n"
      "      randcase\n"
      "        a + b : x = 1;\n"
      "        a - b : x = 2;\n"
      "        a ^ ~b : x = 3;\n"
      "        12'h800 : x = 4;\n"
      "      endcase\n"
      "      if (x == 4) n++;\n"
      "      if (x == 2) never++;\n"
      "    end\n"
      "    a = 8'hFF; b = 1;\n"
      "    for (i = 0; i < 1000; i++) begin\n"
      "      x = 0;\n"
      "      randcase\n"
      "        a + b : x = 1;\n"
      "        a - b : x = 2;\n"
      "        a ^ ~b : x = 3;\n"
      "        12'h800 : x = 4;\n"
      "      endcase\n"
      "      if (x == 1) wrapped++;\n"
      "    end\n"
      "    randcase\n"
      "      bump() : x = 1;\n"
      "      bump() : x = 2;\n"
      "    endcase\n"
      "    mostly = n > 800;\n"
      "    no_second = never == 0;\n"
      "    no_wrapped = wrapped == 0;\n"
      "    $display(\"%0d %0d %0d %0d\", mostly, no_second, no_wrapped, "
      "calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 2\n");
}

TEST(RandcaseRun, ASeededThreadSelectsTheSameBranchesBesideABusyOne) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, f1[8], f2[8], busy, stable = 1;\n"
      "  function automatic int pick();\n"
      "    int y = 0;\n"
      "    randcase\n"
      "      3 : y = 1;\n"
      "      1 : y = 2;\n"
      "      4 : y = 3;\n"
      "    endcase\n"
      "    return y;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        automatic process p = process::self();\n"
      "        p.srandom(3);\n"
      "        for (int j = 0; j < 8; j++) f1[j] = pick();\n"
      "      end\n"
      "    join\n"
      "    fork\n"
      "      begin\n"
      "        automatic process q = process::self();\n"
      "        q.srandom(5);\n"
      "        for (int j = 0; j < 100; j++) busy = pick();\n"
      "      end\n"
      "      begin\n"
      "        automatic process p = process::self();\n"
      "        p.srandom(3);\n"
      "        for (int j = 0; j < 8; j++) f2[j] = pick();\n"
      "      end\n"
      "    join\n"
      "    for (i = 0; i < 8; i++) if (f1[i] != f2[i]) stable = 0;\n"
      "    $display(\"%0d\", stable);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(RandcaseRun, ARandcaseInAFunctionBodyWeighsWithTheFunctionsArguments) {
  SimFixture f;
  std::string out = RunCapture(
      "function int F(int y);\n"
      "  int a;\n"
      "  randcase\n"
      "    y - y : a = 5;\n"
      "    y + y : a = 10;\n"
      "  endcase\n"
      "  return a;\n"
      "endfunction\n"
      "module t;\n"
      "  initial $display(\"%0d\", F(6));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10\n");
}

}  // namespace
