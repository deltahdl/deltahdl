#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ForeachDimensionSim, APackedVectorIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int order;\n"
      "  initial begin\n"
      "    order = 0;\n"
      "    foreach (v[i]) order = order * 10 + i;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 76543210u);
}

TEST(ForeachDimensionSim, AnAscendingPackedVectorIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:4] u;\n"
      "  int order;\n"
      "  initial begin\n"
      "    order = 0;\n"
      "    foreach (u[i]) order = order * 10 + i;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1234u);
}

TEST(ForeachDimensionSim, EachUnpackedDimensionIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int A [3:1][2];\n"
      "  longint order;\n"
      "  initial begin\n"
      "    order = 0;\n"
      "    foreach (A[i, j]) order = order * 100 + i * 10 + j;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 303120211011u);
}

TEST(ForeachDimensionSim, ThePackedDimensionsFollowTheUnpackedOnes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [3:0][2:1] B [5:1][4];\n"
      "  int n, first, last;\n"
      "  initial begin\n"
      "    n = 0;\n"
      "    foreach (B[q, r, , s]) begin\n"
      "      if (n == 0) first = q * 100 + r * 10 + s;\n"
      "      last = q * 100 + r * 10 + s;\n"
      "      n++;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* n = f.ctx.FindVariable("n");
  auto* first = f.ctx.FindVariable("first");
  auto* last = f.ctx.FindVariable("last");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 40u);
  EXPECT_EQ(first->value.ToUint64(), 502u);
  EXPECT_EQ(last->value.ToUint64(), 131u);
}

TEST(ForeachDimensionSim, TheSecondVariableWalksTheElementsPackedDimension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] M [2];\n"
      "  longint order;\n"
      "  initial begin\n"
      "    order = 0;\n"
      "    foreach (M[i, j]) order = order * 10 + j;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7654321076543210u);
}

TEST(ForeachDimensionSim, AFunctionBodyWalksTheDeclaredIndices) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int A [3:1];\n"
      "  function int f();\n"
      "    int order;\n"
      "    order = 0;\n"
      "    foreach (A[i]) order = order * 10 + i;\n"
      "    return order;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 321u);
}

TEST(ForeachDimensionSim, AFunctionBodyWalksAPackedVectorFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  function int f();\n"
      "    int order;\n"
      "    order = 0;\n"
      "    foreach (v[i]) order = order * 10 + i;\n"
      "    return order;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 76543210u);
}

TEST(ForeachDimensionSim, AFunctionBodyNestsOverEveryNamedDimension) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [3:0][2:1] B [5:1][4];\n"
      "  function int f();\n"
      "    int n, first, last;\n"
      "    n = 0;\n"
      "    foreach (B[q, r, , s]) begin\n"
      "      if (n == 0) first = q * 100 + r * 10 + s;\n"
      "      last = q * 100 + r * 10 + s;\n"
      "      n++;\n"
      "    end\n"
      "    return n * 1000000 + first * 1000 + last;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 40502131u);
}

TEST(ForeachDimensionSim, ADescendingPropertyIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  int p[3:1];\n"
      "  function int walk();\n"
      "    int order;\n"
      "    order = 0;\n"
      "    foreach (p[i]) order = order * 10 + i;\n"
      "    return order;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  int x;\n"
      "  initial begin c = new; x = c.walk(); end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 321u);
}

TEST(ForeachDimensionSim, ADescendingPropertyIsWalkedDownThroughAHandle) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  int p[3:1];\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  int order;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    order = 0;\n"
      "    foreach (c.p[i]) order = order * 10 + i;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 321u);
}

TEST(ForeachDimensionSim, EachDimensionOfAPropertyIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  int g[2:1][2];\n"
      "  function int walk();\n"
      "    int order;\n"
      "    order = 0;\n"
      "    foreach (g[i, j]) order = order * 100 + i * 10 + j;\n"
      "    return order;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  int x;\n"
      "  initial begin c = new; x = c.walk(); end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20211011u);
}

TEST(ForeachDimensionSim, ADescendingStructureMemberIsWalkedFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int v[3:1]; } s_t;\n"
      "  s_t s;\n"
      "  int order;\n"
      "  initial begin\n"
      "    order = 0;\n"
      "    foreach (s.v[i]) order = order * 10 + i;\n"
      "  end\n"
      "endmodule\n",
      f, "order");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 321u);
}

TEST(ForeachDimensionSim, AFunctionBodyWalksADescendingStructureMemberDown) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int v[3:1]; } s_t;\n"
      "  s_t s;\n"
      "  function int f();\n"
      "    int order;\n"
      "    order = 0;\n"
      "    foreach (s.v[i]) order = order * 10 + i;\n"
      "    return order;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 321u);
}

TEST(ForeachLoopVariableSim, LoopVariableOfAnArrayOrQueueIsSignedInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a [-2:2];\n"
      "  int q [$] = '{1, 2};\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    foreach (a[i]) if (i < 0) r += 10;\n"
      "    foreach (q[i]) if (i - 1 < 0) r += 1;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(ForeachLoopVariableSim, LoopVariableInAFunctionIsSignedInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a [-2:2];\n"
      "  int q [$] = '{1, 2};\n"
      "  int r;\n"
      "  function automatic int count();\n"
      "    int c = 0;\n"
      "    foreach (a[i]) if (i < 0) c += 10;\n"
      "    foreach (q[i]) if (i - 1 < 0) c += 1;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial r = count();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

TEST(ForeachLoopVariableSim, ForeachOverAStringInAFunctionStepsPerCharacter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  function automatic int f(string s);\n"
      "    int c = 0;\n"
      "    foreach (s[i]) c++;\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial r = f(\"ab\");\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(ForeachLoopVariableSim, SecondLoopVariableOverAQueueOfArraysInAFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r [$][2];\n"
      "  int s;\n"
      "  function automatic int sum();\n"
      "    int t = 0;\n"
      "    foreach (r[k, j]) t += r[k][j] * (j + 1);\n"
      "    return t;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r.push_back('{1, 2});\n"
      "    r.push_back('{3, 4});\n"
      "    s = sum();\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(ForeachLoopExampleSim, TheWordsExamplePrintsEachIndexAndValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string words [2] = '{ \"hello\", \"world\" };\n"
                       "  initial\n"
                       "    foreach( words[j] )\n"
                       "      $display( j , words[j] );\n"
                       "endmodule\n",
                       f),
            "          0hello\n          1world\n");
}

TEST(ForeachLoopExampleSim, TheProdExampleInitializesEveryElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int prod [1:8] [1:3];\n"
                 "  int s;\n"
                 "  initial begin\n"
                 "    foreach( prod[k, m] )\n"
                 "      prod[k][m] = k * m;\n"
                 "    foreach (prod[k, m]) s += prod[k][m];\n"
                 "    $display(\"%0d %0d %0d\", prod[1][1], prod[8][3], s);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 24 216\n");
}

TEST(ForeachLoopExampleSim, TheFirstCardinalityExampleNestsIOutsideK) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  int A [2][3][4];\n"
          "  initial begin\n"
          "    foreach( A [ i, j, k ] ) $write(\"%0d%0d%0d \", i, j, k);\n"
          "    $display;\n"
          "  end\n"
          "endmodule\n",
          f),
      "000 001 002 003 010 011 012 013 020 021 022 023 100 101 102 103 110 111 "
      "112 113 120 121 122 123 \n");
}

TEST(ForeachLoopExampleSim, TheSecondCardinalityExampleSkipsTheThirdIndex) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  bit [3:0][2:1] B [5:1][4];\n"
                 "  int n;\n"
                 "  initial begin\n"
                 "    foreach( B [ q, r, , s ] ) begin\n"
                 "      if (n < 3 || n > 36) $write(\"%0d%0d%0d \", q, r, s);\n"
                 "      n++;\n"
                 "    end\n"
                 "    $display(\"%0d\", n);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "502 501 512 121 132 131 40\n");
}

TEST(ForeachLoopLifetimeSim, ALoopVariableIsAutomaticInAStaticTask) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a [3];\n"
                       "  task static walk;\n"
                       "    foreach (a[i])\n"
                       "      #1 $display(\"%0d\", i);\n"
                       "  endtask\n"
                       "  initial fork\n"
                       "    walk;\n"
                       "    walk;\n"
                       "  join\n"
                       "endmodule\n",
                       f),
            "0\n0\n1\n1\n2\n2\n");
}

}  // namespace
