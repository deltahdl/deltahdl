#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.7.3 walks each dimension from its declared left bound to its right
// bound. Each test folds the loop variables into one number in the order the
// loop visits them, so a walk in the wrong direction, over the wrong
// dimensions or with the wrong indices gives a different number.

// The one packed dimension of a vector, `[7:0]`, counts down from 7.
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

// An ascending packed range, `[1:4]`, counts up from its left bound, which is
// not 0.
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

// The descending first dimension of a multidimensional array, `[3:1]`, counts
// down while the second, `[2]`, counts up inside it.
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

// The dimensions are numbered unpacked first, then packed, so for
// `bit [3:0][2:1] B [5:1][4]` the variables `q, r, , s` name `[5:1]`, `[4]`
// and `[2:1]`, skipping `[3:0]`: 5 * 4 * 2 sets, from 5,0,2 to 1,3,1.
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

// A one-dimensional array's element with one packed dimension: the second
// variable walks the element's `[7:0]` inside each element.
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

// §13.4 lets a function body hold the loop, and there it walks the same
// indices: `[3:1]` gives 3, 2, 1, not 0, 1, 2.
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

// A packed vector in a function body counts down from its left bound.
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

// A function body nests over a declared array's dimensions, packed ones
// included, as a process does.
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

// §8.5 puts no limit on a property's type, so a property declared `[3:1]` is
// walked 3, 2, 1 like a variable, in a method over the bare name.
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

// The same property walked from a process through a handle.
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

// Each dimension of a property with more than one is walked from its own left
// bound: `[2:1]` counts down while `[2]` counts up inside it.
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

// §7.2 lets a structure member be an unpacked array, and its `[3:1]` is
// walked 3, 2, 1.
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

// The same member walked in a function body.
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

}  // namespace
