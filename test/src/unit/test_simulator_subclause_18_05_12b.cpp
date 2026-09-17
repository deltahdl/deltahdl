#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's D, and the head of a class holding two D handles a and b
// beside a rand int x and y, which each example's constraint completes.
const char* const kGuardedHead =
    "class D;\n"
    "  int x;\n"
    "endclass\n"
    "class C;\n"
    "  rand int x, y;\n"
    "  D a, b;\n";

// 18.5.12, Example 1, case 2: a is null, so every guard subexpression
// reading a is an ERROR and none of the disjuncts is TRUE to sift it; an
// error is generated and randomize() fails, where a solver reading the
// nonexistent a.x as a value would have solved the object, as the design
// test/src/e2e/constraint_guards.sv runs it.
TEST(ConstraintGuardsRun, ANullHandleInTheGuardFailsRandomize) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  initial begin\n"
          "    C o = new;\n"
          "    D b = new;\n"
          "    o.b = b;\n"
          "    $display(\"%0d\", o.randomize());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// 18.5.12, Example 1, case 1: a.x is 5 and b is null. The disjunct a.x == 5
// is TRUE, so the ERROR of b.x is sifted away and the unconditional
// constraint x + y == 10 is generated: every one of 32 draws solves and
// sums to 10, and some draw has x at or above y, which a conditional
// constraint under x < y would not hold to the sum.
TEST(ConstraintGuardsRun, ATrueDisjunctSiftsTheNullHandleAway) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y || a.x > b.x || a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0, apart = 0;\n"
          "  initial begin\n"
          "    C o = new;\n"
          "    D a = new;\n"
          "    a.x = 5;\n"
          "    o.a = a;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize()) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "      if (o.x >= o.y) apart++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d\", ok, sums, apart > 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

// 18.5.12, Example 2, case 1: a.x is 6 and b is null. The conjunct a.x == 5
// is FALSE, so the ERROR of b.x is sifted away and the constraint is
// eliminated with no error: every draw solves, and x and y drawn free over
// the ints sum to 10 as good as never.
TEST(ConstraintGuardsRun, AFalseConjunctEliminatesTheConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0;\n"
          "  initial begin\n"
          "    C o = new;\n"
          "    D a = new;\n"
          "    a.x = 6;\n"
          "    o.a = a;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize()) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", ok, sums);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 0\n");
}

// 18.5.12, Example 2, case 3: a.x is 5 and b.x is 2. Every guard
// subexpression over the state is TRUE and x < y is RANDOM, so the
// conditional constraint (x < y) -> x + y == 10 is generated: under an
// inline x < y every one of 32 draws sums to 10.
TEST(ConstraintGuardsRun, ARandomGuardGeneratesTheConditionalConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && a.x > b.x && a.x == 5) -> x + y == 10; "
          "}\n"
          "endclass\n"
          "module t;\n"
          "  int ok = 0, sums = 0;\n"
          "  initial begin\n"
          "    C o = new;\n"
          "    D a = new;\n"
          "    D b = new;\n"
          "    a.x = 5;\n"
          "    b.x = 2;\n"
          "    o.a = a;\n"
          "    o.b = b;\n"
          "    repeat (32) begin\n"
          "      if (o.randomize() with { x < y; }) ok++;\n"
          "      if (o.x + o.y == 10) sums++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", ok, sums);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.5.12, Example 3, case 2: a.x is 8 and b is null. The nested
// disjunction (a.x > b.x || a.x == 5) is (ERROR || FALSE), which is ERROR,
// and conjoined with the RANDOM x < y stays ERROR, so randomize() fails.
TEST(ConstraintGuardsRun, AnErrorNoOperandSiftsFailsRandomize) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGuardedHead) +
          "  constraint c1 { (x < y && (a.x > b.x || a.x == 5)) -> x + y == "
          "10; }\n"
          "endclass\n"
          "module t;\n"
          "  initial begin\n"
          "    C o = new;\n"
          "    D a = new;\n"
          "    a.x = 8;\n"
          "    o.a = a;\n"
          "    $display(\"%0d\", o.randomize());\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// 18.5.12: the clause's SList, sorted under if (next != null) n < next.n.
// The guard is FALSE on the tail, whose next is null, so its constraint is
// eliminated rather than failing on the nonexistent handle, and TRUE on the
// two nodes before it, whose constraints are generated: over 32 draws of
// the three-node list as one whole every draw solves and ascends, and the
// tail, held above the second alone, draws above zero in some draw.
TEST(ConstraintGuardsRun, TheGuardedSortEliminatesTheTailsConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      "class SList;\n"
      "  rand int n;\n"
      "  rand SList next;\n"
      "  constraint sort { if (next != null) n < next.n; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, ordered = 0, above = 0;\n"
      "  initial begin\n"
      "    SList head = new;\n"
      "    SList second = new;\n"
      "    SList tail = new;\n"
      "    head.next = second;\n"
      "    second.next = tail;\n"
      "    repeat (32) begin\n"
      "      if (head.randomize()) ok++;\n"
      "      if (head.n < second.n && second.n < tail.n) ordered++;\n"
      "      if (tail.n > 0) above++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", ok, ordered, above > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 1\n");
}

}  // namespace
