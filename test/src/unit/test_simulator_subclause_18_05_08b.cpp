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

}  // namespace
