#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A class C holding the members `decls`, randomized `draws` times by an
// initial that counts the draws for which `holds` is true, as the design
// test/src/e2e/foreach_iterative_constraints.sv does, and displays the count
// and `after`, an expression read once the draws are done.
std::string Counting(const std::string& decls, int draws,
                     const std::string& holds, const std::string& after) {
  return "class C;\n" + decls +
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
         "    $display(\"%0d %0d\", held, " +
         after +
         ");\n"
         "  end\n"
         "endmodule\n";
}

// 18.5.7.1: the size method of a dynamic array can be used to constrain the
// size of the array, and the size constraints are solved first. The
// clause's c1 holds A.size inside {[1:10]}, so every one of 64 draws leaves
// A holding 1 to 10 elements, read through size() and through the element
// past the last, which reads as no element does, and more than one size is
// drawn, which an array kept at the size it had would never show.
TEST(ForeachIterativeConstraintsRun, ASizeConstraintSizesTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size inside {[1:10]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, smallest = 11, largest = 0;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.A.size() >= 1 && o.A.size() <= 10) held++;\n"
      "      if (o.A.size() < smallest) smallest = o.A.size();\n"
      "      if (o.A.size() > largest) largest = o.A.size();\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, largest > smallest);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

// 18.5.7.1: a predicate over a loop variable and the size of the array
// iterated behaves as a guard against the creation of a constraint, so the
// clause's c2 holds each element above the one before it for the indexes
// below the last alone, and every one of 64 draws is sorted ascending
// whatever its size, which a foreach imposing its set on every index, the
// last element held below an element the array lacks, would fail on.
TEST(ForeachIterativeConstraintsRun, APredicateGuardsTheConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size inside {[1:10]}; }\n"
      "  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; "
      "}\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ok = 0, longest = 0;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      ok = 1;\n"
      "      for (int i = 1; i < o.A.size(); i++)\n"
      "        if (o.A[i] <= o.A[i - 1]) ok = 0;\n"
      "      if (ok) held++;\n"
      "      if (o.A.size() > longest) longest = o.A.size();\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, longest > 4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

// 18.5.7.1: the size method is a state variable within the foreach block of
// the array, solved ahead of the iterative constraints, so a foreach holding
// each element to the size plus its index over an array held to 3 elements
// reads the size as 3 and draws 3, 4 and 5, which the size read as anything
// but the value drawn for it would not give.
TEST(ForeachIterativeConstraintsRun, TheSizeIsAStateVariableInTheForeach) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size == 3; }\n"
      "  constraint c2 { foreach (A[i]) A[i] == A.size + i; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d\", o.A.size(), o.A[0], o.A[1], o.A[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3 4 5\n");
}

// 18.5.7.1/18.4: a dynamic array whose size no constraint holds keeps the
// size new[] gave it, its elements alone randomized, so a foreach over it
// iterates the 5 elements the array holds and holds each to three times its
// index; a second new[] of 2 leaves 2 elements to iterate, and delete()
// none, which the size reports.
TEST(ForeachIterativeConstraintsRun, AnUnconstrainedSizeIsKept) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint each { foreach (A[i]) A[i] == i * 3; }\n"
      "  function void resize(int n);\n"
      "    A = new[n];\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    o.resize(5);\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", o.A.size(), o.A[0], o.A[1],\n"
      "             o.A[2], o.A[3], o.A[4]);\n"
      "    o.A = new[2];\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d\", o.A.size(), o.A[0], o.A[1]);\n"
      "    o.A.delete();\n"
      "    $display(\"%0d\", o.A.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 0 3 6 9 12\n2 0 3\n0\n");
}

// 18.5.7.1: an index expression can include loop variables, constants and
// state variables, and a predicate over a loop variable and a state variable
// is a guard: with off a state variable holding 2, each element from index
// 2 on is held to one more than the element off places before it, and over
// 32 draws every draw holds B[2] one above B[0] and B[3] one above B[1].
TEST(ForeachIterativeConstraintsRun, AnIndexExpressionMayHoldAStateVariable) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int B[4];\n"
               "  int off = 2;\n"
               "  constraint range { foreach (B[i]) B[i] inside {[0:99]}; }\n"
               "  constraint step { foreach (B[i]) (i >= off) -> B[i] == B[i - "
               "off] + 1; }\n",
               32, "o.B[2] == o.B[0] + 1 && o.B[3] == o.B[1] + 1",
               "o.B[0] < 100"),
      f);
  EXPECT_EQ(out, "32 1\n");
}

// 18.5.7.1: the scope of each loop variable is the foreach constraint
// construct, so a loop variable named as a property of the class is the
// index within the foreach and the property outside it: each element is
// held to one more than its index, which a k read as the property's 100
// would put beyond a 4-bit element, and the property keeps its 100.
TEST(ForeachIterativeConstraintsRun, TheLoopVariableShadowsAProperty) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] A[3];\n"
      "  int k = 100;\n"
      "  constraint c { foreach (A[k]) A[k] == k + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d\", o.A[0], o.A[1], o.A[2], o.k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 100\n");
}

}  // namespace
