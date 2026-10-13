#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's leaf and heap node classes, a leaf holding a byte v and a
// heap node extending it with a rand left and right subtree under heapcond,
// as the design test/src/e2e/global_constraints.sv declares them.
const char* const kHeapClasses =
    "class Leaf;\n"
    "  rand bit [7:0] v;\n"
    "endclass\n"
    "class Heap extends Leaf;\n"
    "  rand Leaf left;\n"
    "  rand Leaf right;\n"
    "  constraint heapcond { left.v <= v; right.v > v; }\n"
    "  function new();\n"
    "    left = new;\n"
    "    right = new;\n"
    "  endfunction\n"
    "endclass\n";

// 18.5.8: the objects randomized as a whole are found recursively, so a heap
// node whose left subtree is a heap node in turn is solved with it, the
// inner node's own heapcond holding at once with the outer's on every one of
// 32 draws, which a solve that stopped at the outer node's leaves, leaving
// the inner node's subtrees where they stood at 0 against a v drawn above
// them, would fail on the inner node's right leaf.
TEST(GlobalConstraintsRun, AHeapNodeUnderAHeapNodeIsSolvedWithIt) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kHeapClasses) +
          "module t;\n"
          "  int held = 0;\n"
          "  initial begin\n"
          "    Heap outer = new;\n"
          "    Heap inner = new;\n"
          "    outer.left = inner;\n"
          "    repeat (32) begin\n"
          "      void'(outer.randomize());\n"
          "      if (outer.left.v <= outer.v && outer.right.v > outer.v &&\n"
          "          inner.left.v <= inner.v && inner.right.v > inner.v)\n"
          "        held++;\n"
          "    end\n"
          "    $display(\"%0d\", held);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32\n");
}

// 18.5.8: the random variables of a rand object member are randomized along
// with the containing object's, so over 32 draws of a heap node the leaves'
// values vary as the node's does, while both global constraints hold on
// every draw; leaves left as they were constructed would hold 0 throughout.
TEST(GlobalConstraintsRun, TheLeavesAreDrawnWithTheNode) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kHeapClasses) +
                     "module t;\n"
                     "  int held = 0, first = -1, varies = 0;\n"
                     "  initial begin\n"
                     "    Heap h = new;\n"
                     "    repeat (32) begin\n"
                     "      void'(h.randomize());\n"
                     "      if (h.left.v <= h.v && h.right.v > h.v) held++;\n"
                     "      if (first < 0) first = h.right.v;\n"
                     "      else if (h.right.v != first) varies = 1;\n"
                     "    end\n"
                     "    $display(\"%0d %0d\", held, varies);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 1\n");
}

// §18.5.8 with §18.4: the objects a rand array of handles holds are random
// object members as a scalar handle's object is, so a Grid holding both
// solves all three Cells with it, each drawn into its own range.
TEST(GlobalConstraintsRun, TheObjectsOfAnArrayOfHandlesAreSolvedWithTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Cell;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { y inside {[1:100]}; }\n"
      "endclass\n"
      "class Grid;\n"
      "  rand Cell s;\n"
      "  rand Cell arr[];\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static Grid g = new;\n"
      "    g.s = new;\n"
      "    g.arr = new[2];\n"
      "    g.arr[0] = new; g.arr[1] = new;\n"
      "    $display(\"%0d %0d %0d %0d\", g.randomize(), g.s.y inside "
      "{[1:100]},\n"
      "             g.arr[0].y inside {[1:100]}, g.arr[1].y inside "
      "{[1:100]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n");
}

// §18.5.8 with §18.4 and §18.5.7.1: an object solved together with its
// random object members keeps its rand dynamic array, sized by its size
// constraint and its elements drawn under its foreach constraint.
TEST(GlobalConstraintsRun, ATreesDynamicArrayIsSizedAndDrawn) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "class A;\n"
      "  rand B b;\n"
      "  rand bit [7:0] q[];\n"
      "  constraint s { q.size() == 3; foreach (q[i]) q[i] inside {[1:5]}; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    a.b = new;\n"
      "    $display(\"%0d %0d %0d\", a.randomize(), a.q.size(),\n"
      "             a.q[0] inside {[1:5]} && a.q[1] inside {[1:5]} &&\n"
      "                 a.q[2] inside {[1:5]});\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 3 1\n");
}

// §18.5.8 with §18.5.3 and §18.5.4: an object solved together with its
// random object members keeps its dist and uniqueness constraints, so on
// every one of 16 calls d takes the only value of nonzero weight and u and
// v differ.
TEST(GlobalConstraintsRun, ATreesDistAndUniquenessConstraintsHold) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "class A;\n"
      "  rand B b;\n"
      "  rand bit [1:0] d, u, v;\n"
      "  constraint c {\n"
      "    d dist { 0 := 0, 1 := 1, 2 := 0, 3 := 0 };\n"
      "    unique { u, v };\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    a.b = new;\n"
      "    repeat (16)\n"
      "      if (a.randomize() == 1 && a.d == 1 && a.u != a.v) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16\n");
}

// §18.5.8: a random object member solved with its container keeps every
// form of its own constraints -- a sized dynamic array under foreach and a
// reduction, an implication discarding a soft constraint, a derived
// equality, a solve...before ordering, a function of a random variable,
// uniqueness, an if-else and a guard over state -- and the container's
// inline constraint applies with them, on each of 8 calls.
TEST(GlobalConstraintsRun, AMembersOwnConstraintsHoldInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit [7:0] e[];\n"
      "  rand bit s;\n"
      "  rand bit [3:0] t, w, a1, a2;\n"
      "  rand bit [7:0] z;\n"
      "  rand bit [1:0] m, n;\n"
      "  int lim = 1;\n"
      "  function bit [7:0] twice(bit [3:0] a); return a * 2; endfunction\n"
      "  constraint k { e.size() == 2; foreach (e[i]) e[i] == i + 7; "
      "e.sum() == 15; }\n"
      "  constraint o { s -> t == 0; soft t == 9; w == t + 1; }\n"
      "  constraint p { a1 < 10; a2 == a1 + 1; solve a1 before a2; }\n"
      "  constraint f { z == twice(a1); }\n"
      "  constraint q {\n"
      "    unique { m, n };\n"
      "    if (s) m < 3; else m < 3;\n"
      "    (lim > 0 && lim < 5) -> n < 3;\n"
      "  }\n"
      "endclass\n"
      "class A;\n"
      "  rand bit [7:0] x;\n"
      "  rand B b;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ok;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    a.b = new;\n"
      "    repeat (8) begin\n"
      "      ok = a.randomize() with { x == 3; };\n"
      "      if (ok == 1 && a.x == 3 && a.b.e.size() == 2 && a.b.e[0] == 7 &&\n"
      "          a.b.e[1] == 8 && a.b.t == (a.b.s ? 0 : 9) &&\n"
      "          a.b.w == a.b.t + 1 && a.b.a1 < 10 && a.b.a2 == a.b.a1 + 1 &&\n"
      "          a.b.z == a.b.a1 * 2 && a.b.m != a.b.n && a.b.m < 3 &&\n"
      "          a.b.n < 3)\n"
      "        held++;\n"
      "    end\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8\n");
}

}  // namespace
