#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls` under the constraint blocks
// `constraints`, randomized `draws` times by an initial that counts the draws
// for which `holds` is true, as the design
// test/src/e2e/iterative_constraints.sv does, and displays the count.
std::string Counting(const std::string& decls, const std::string& constraints,
                     int draws, const std::string& holds) {
  return "class C;\n" + decls + constraints +
         "endclass\n"
         "module t;\n"
         "  int held = 0;\n"
         "  initial begin\n"
         "    C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n"
         "      if (" +
         holds +
         ") held++;\n"
         "    end\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

// 18.5.7: an arrayed variable is constrained through a loop variable and an
// indexing expression. The clause's C1, a foreach holding each element of A
// inside {2, 4, 8, 16}, holds every element of every draw in the set, which
// an array the object held as one value, or a foreach that imposed nothing,
// would not.
TEST(IterativeConstraintsRun, AForeachConstrainsEveryElement) {
  SimFixture f;
  std::string out = RunCapture(
      Counting(
          "  rand byte A[4];\n",
          "  constraint C1 { foreach (A[i]) A[i] inside {2, 4, 8, 16}; }\n", 32,
          "o.A[0] inside {2, 4, 8, 16} && o.A[1] inside {2, 4, 8, 16} && "
          "o.A[2] inside {2, 4, 8, 16} && o.A[3] inside {2, 4, 8, 16}"),
      f);
  EXPECT_EQ(out, "32\n");
}

// 18.5.7: the loop variable is the element's index, so the clause's C2, each
// element above twice its index, holds A[3] above 6 while A[0] is free above
// 0: over 64 draws of 4-bit elements every draw holds the relation and A[0]
// is drawn at or below 6 at least once, which the last index standing for
// every element would never allow.
TEST(IterativeConstraintsRun, TheLoopVariableIsTheIndex) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] A[4];\n"
      "  constraint C2 { foreach (A[j]) A[j] > 2 * j; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, low = 0;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.A[0] > 0 && o.A[1] > 2 && o.A[2] > 4 && o.A[3] > 6) "
      "held++;\n"
      "      if (o.A[0] <= 6) low++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, low > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

// 18.5.7: an arrayed variable is constrained through an array reduction
// method. Three elements each below 10 whose sum is held to 12 add up to 12
// on every draw, read back element by element and through the same sum()
// on the object from outside the class.
TEST(IterativeConstraintsRun, AReductionMethodConstrainsTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand bit [7:0] B[3];\n",
               "  constraint each { foreach (B[k]) B[k] < 10; }\n"
               "  constraint total { B.sum() == 12; }\n",
               32,
               "o.B[0] + o.B[1] + o.B[2] == 12 && o.B.sum() == 12 && "
               "o.B[0] < 10 && o.B[1] < 10 && o.B[2] < 10"),
      f);
  EXPECT_EQ(out, "32\n");
}

// 18.5.7 constrains the elements a class holds one by one: a property
// declared as an array is written and read element by element, from a method
// of the class and through a handle, its size() the count it declared, and
// an element never written its type's initial value.
TEST(IterativeConstraintsRun, TheElementsAreHeldOneByOne) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  int v[3];\n"
      "  function void fill(int base);\n"
      "    v[1] = base;\n"
      "    v[2] = v[1] + 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    o.fill(7);\n"
      "    o.v[2] = o.v[2] * 2;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", o.v[0], o.v[1], o.v[2], "
      "o.v.size(), o.v.sum());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 7 16 3 23\n");
}

}  // namespace
