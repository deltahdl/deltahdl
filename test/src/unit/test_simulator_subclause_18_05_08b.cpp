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
          "    static Heap outer = new;\n"
          "    static Heap inner = new;\n"
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
                     "    static Heap h = new;\n"
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

// Runs 4 calls of `call` on an A holding a rand x and a rand B whose body is
// `body`, and displays how many returned 1 with `check` holding.
std::string RunMemberOfATree(const std::string& body, const std::string& call,
                             const std::string& check) {
  SimFixture f;
  return RunCapture("class B;\n" + body +
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
                        "    repeat (4) begin\n"
                        "      ok = " +
                        call +
                        ";\n"
                        "      if (ok == 1 && " +
                        check +
                        ") held++;\n"
                        "    end\n"
                        "    $display(\"%0d\", held);\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

// §18.5.8 with §18.4, §18.5.7.1 and §18.5.7.2: a random object member solved
// with its container keeps its rand dynamic array, sized, its elements drawn
// under foreach and summed under a reduction, while the container's inline
// constraint applies with them.
TEST(GlobalConstraintsRun, AMembersDynamicArrayHoldsInTheTree) {
  EXPECT_EQ(RunMemberOfATree(
                "  rand bit [7:0] e[];\n"
                "  constraint k { e.size() == 2; foreach (e[i]) e[i] == i + 7; "
                "e.sum() == 15; }\n",
                "a.randomize() with { x == 3; }",
                "a.x == 3 && a.b.e.size() == 2 && a.b.e[0] == 7 && "
                "a.b.e[1] == 8"),
            "4\n");
}

// §18.5.8 with §18.5.13: a random object member solved with its container
// keeps its soft constraint, discarded where its implication forbids it,
// and the equality deriving w from t.
TEST(GlobalConstraintsRun, AMembersSoftConstraintHoldsInTheTree) {
  EXPECT_EQ(RunMemberOfATree("  rand bit s;\n"
                             "  rand bit [3:0] t, w;\n"
                             "  constraint o { s -> t == 0; soft t == 9; "
                             "w == t + 1; }\n",
                             "a.randomize()",
                             "a.b.t == (a.b.s ? 0 : 9) && a.b.w == a.b.t + 1"),
            "4\n");
}

// §18.5.8 with §18.5.9 and §18.5.11: a random object member solved with its
// container keeps its solve...before ordering and the priority a function
// of a random variable gives its argument.
TEST(GlobalConstraintsRun, AMembersOrderingsHoldInTheTree) {
  EXPECT_EQ(
      RunMemberOfATree(
          "  rand bit [3:0] a1, a2;\n"
          "  rand bit [7:0] z;\n"
          "  function bit [7:0] twice(bit [3:0] a); return a * 2; "
          "endfunction\n"
          "  constraint p { a1 < 10; a2 == a1 + 1; solve a1 before a2; }\n"
          "  constraint f { z == twice(a1); }\n",
          "a.randomize()",
          "a.b.a1 < 10 && a.b.a2 == a.b.a1 + 1 && a.b.z == a.b.a1 * 2"),
      "4\n");
}

// §18.5.8 with §18.5.4, §18.5.6 and §18.5.12: a random object member solved
// with its container keeps its uniqueness constraint, its if-else and its
// implication guarded by state.
TEST(GlobalConstraintsRun, AMembersUniquenessAndGuardsHoldInTheTree) {
  EXPECT_EQ(RunMemberOfATree("  rand bit s;\n"
                             "  rand bit [1:0] m, n;\n"
                             "  int lim = 1;\n"
                             "  constraint q {\n"
                             "    unique { m, n };\n"
                             "    if (s) m < 3; else m < 3;\n"
                             "    (lim > 0 && lim < 5) -> n < 3;\n"
                             "  }\n",
                             "a.randomize()",
                             "a.b.m != a.b.n && a.b.m < 3 && a.b.n < 3"),
            "4\n");
}

// §18.5.8 with §18.5.7.1: a foreach constraint of an object two levels into
// the tree whose relations reach the object under its handle l ties each
// element to the l.v the call draws, on every one of 4 calls, rather than
// to the l.v held before it.
TEST(GlobalConstraintsRun, AForeachReachingAnotherObjectHoldsInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit [3:0] v;\n"
      "endclass\n"
      "class Mid;\n"
      "  rand Leaf l;\n"
      "  rand bit [3:0] a[2];\n"
      "  constraint c { foreach (a[i]) a[i] == l.v + i; }\n"
      "  function new(); l = new; endfunction\n"
      "endclass\n"
      "class Top;\n"
      "  rand Mid m;\n"
      "  function new(); m = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static Top o = new;\n"
      "    repeat (4)\n"
      "      if (o.randomize() == 1 && o.m.a[0] == o.m.l.v &&\n"
      "          o.m.a[1] == o.m.l.v + 1) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §18.5.8 with §18.5.3: a dist whose target is the random variable of the
// object under the handle left weights that variable, so on every one of 4
// calls left.v takes the only value of nonzero weight.
TEST(GlobalConstraintsRun, ADistOnAnotherObjectsVariableHoldsInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit [1:0] v;\n"
      "endclass\n"
      "class A;\n"
      "  rand Leaf left;\n"
      "  constraint c { left.v dist { 0 := 0, 1 := 0, 2 := 1, 3 := 0 }; }\n"
      "  function new(); left = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    repeat (4)\n"
      "      if (a.randomize() == 1 && a.left.v == 2) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §18.5.8 with §18.5.4: a uniqueness constraint naming the random variable
// of the object under the handle left among its members keeps it apart from
// the others, so on every one of 4 calls the four 2-bit members are
// pairwise distinct.
TEST(GlobalConstraintsRun,
     AUniquenessOverAnotherObjectsVariableHoldsInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit [1:0] v;\n"
      "endclass\n"
      "class A;\n"
      "  rand Leaf left;\n"
      "  rand bit [1:0] p, q, r;\n"
      "  constraint u { unique { p, q, r, left.v }; }\n"
      "  function new(); left = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    repeat (4)\n"
      "      if (a.randomize() == 1 && a.p != a.q && a.p != a.r &&\n"
      "          a.q != a.r && a.left.v != a.p && a.left.v != a.q &&\n"
      "          a.left.v != a.r) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §18.5.8 with §18.5.9: solve left.s before d has the random variable of the
// object under the handle left chosen first, 0 or 1 with equal probability,
// so over 32 calls it is set near half the time, which a 4-bit d drawn with
// it, the implication leaving s set in one of 17 legal combinations, would
// leave near 2; and d is zero on every call with it set.
TEST(GlobalConstraintsRun, AnOrderingOverAnotherObjectsVariableHoldsInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit s;\n"
      "endclass\n"
      "class B;\n"
      "  rand Leaf left;\n"
      "  rand bit [3:0] d;\n"
      "  constraint c { left.s -> d == 0; }\n"
      "  constraint order { solve left.s before d; }\n"
      "  function new(); left = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int set = 0, wrong = 0;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    repeat (32) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.left.s) set++;\n"
      "      if (o.left.s && o.d != 0) wrong++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", set >= 8 && set <= 24, wrong);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0\n");
}

// §18.5.8 with §18.5.6: an implication whose antecedent reaches the object
// under the handle left imposes its consequent as a relation of its own, so
// with left.s ordered first and set near half the time, a 32-bit d is drawn
// as 0 on every call with it set, which a d tried at random against the
// whole implication would never be.
TEST(GlobalConstraintsRun,
     AnImplicationReachingAnotherObjectImposesItsConsequent) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit s;\n"
      "endclass\n"
      "class B;\n"
      "  rand Leaf left;\n"
      "  rand bit [31:0] d;\n"
      "  constraint c { left.s -> d == 0; }\n"
      "  constraint order { solve left.s before d; }\n"
      "  function new(); left = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int set = 0, wrong = 0;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    repeat (32) begin\n"
      "      if (o.randomize() != 1) wrong++;\n"
      "      if (o.left.s) set++;\n"
      "      if (o.left.s && o.d != 0) wrong++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", set >= 8 && set <= 24, wrong);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0\n");
}

// §18.5.8 with §7.4.6: a relation over the random variable of an object an
// element of a rand array of handles holds, arr[1].y, ties x to the arr[1].y
// the call draws, on every one of 4 calls, rather than to the one held
// before it.
TEST(GlobalConstraintsRun, ARelationOverAnElementsObjectHoldsInTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      "class Cell;\n"
      "  rand bit [3:0] y;\n"
      "endclass\n"
      "class Grid;\n"
      "  rand Cell arr[];\n"
      "  rand bit [4:0] x;\n"
      "  constraint c { x == arr[1].y + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static Grid g = new;\n"
      "    g.arr = new[2];\n"
      "    g.arr[0] = new; g.arr[1] = new;\n"
      "    repeat (4)\n"
      "      if (g.randomize() == 1 && g.x == g.arr[1].y + 1) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

}  // namespace
