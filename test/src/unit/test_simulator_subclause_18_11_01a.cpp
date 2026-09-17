#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.11.1's inline constraint checker end to end. Each
// program elaborates a real class, calls randomize(null) (or randomize() on a
// class with no random variables) from source, and copies the outcome into
// module variables the harness reads -- so the behavior observed is that of
// parse/elaborate/run applying the rule through the production randomize() path
// (eval_randomize.cpp), not a hand-built solver state. 18.4/18.4.2 supply the
// rand/randc declarations the checker holds as state, and 18.5 supplies the
// constraint blocks it evaluates.

// 18.11.1: passing null to randomize() indicates no random variables for the
// duration of the call, so every class member behaves as a state variable and
// randomize() acts as a checker: it evaluates the constraints against the
// current values and returns 1 when they all hold. This mirrors the standard's
// own CA example (a relation between rand and non-rand members). The current
// values satisfy x < v && y > w, so the call returns 1 and neither rand
// variable is drawn afresh -- a generator would have overwritten x and y.
TEST(InlineConstraintChecker,
     NullChecksConstraintAgainstCurrentValuesReturnsOne) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  rand byte y;\n"
      "  byte v;\n"
      "  byte w;\n"
      "  constraint c1 { x < v && y > w; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.x = 1; a.y = 9; a.v = 5; a.w = 3;\n"
      "    okv = a.randomize(null);\n"  // checker: all members are state
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);  // 1 < 5 && 9 > 3 holds
  EXPECT_EQ(RunAndGet(src, "rx"), 1u);   // held as a state variable, not drawn
  EXPECT_EQ(RunAndGet(src, "ry"), 9u);   // held as a state variable, not drawn
}

// 18.11.1: a checker returns 0 as soon as a constraint is not satisfied by the
// current values, and because null suppresses randomization it cannot move a
// variable into a satisfying value -- it simply reports the failure and leaves
// every member as it found it. Here x < v is false with the current values, so
// the call returns 0 and x and y keep the values they came in with.
TEST(InlineConstraintChecker, NullReturnsZeroWhenConstraintViolatedHoldsState) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  rand byte y;\n"
      "  byte v;\n"
      "  byte w;\n"
      "  constraint c1 { x < v && y > w; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.x = 5; a.y = 9; a.v = 3; a.w = 3;\n"
      "    okv = a.randomize(null);\n"  // 5 < 3 is false
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 0u);  // constraint not satisfied
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);   // never randomized
  EXPECT_EQ(RunAndGet(src, "ry"), 9u);   // never randomized
}

// 18.11.1: the null argument forces randomize() to behave as a checker rather
// than a generator. This is the sharpest contrast: with a satisfiable
// constraint (x == 100) that the current value violates, the checker cannot
// solve for the satisfying value -- it holds x as a state variable, so it
// returns 0 and leaves x unchanged. The very same class, randomized without
// null, IS a generator: it draws x == 100 and returns 1. Both objects run from
// the same source, so the difference is attributable solely to the null
// argument.
TEST(InlineConstraintChecker,
     NullSuppressesRandomizationOfSatisfiableConstraint) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  constraint c { x == 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int chk0;\n"
      "  int rx0;\n"
      "  int chk1;\n"
      "  int rx1;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    CA b = new;\n"
      "    a.x = 7;\n"
      "    chk0 = a.randomize(null);\n"  // checker: cannot move x to 100
      "    rx0 = a.x;\n"
      "    b.x = 7;\n"
      "    chk1 = b.randomize();\n"  // generator: solves x == 100
      "    rx1 = b.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "chk0"), 0u);   // checker fails: 7 != 100
  EXPECT_EQ(RunAndGet(src, "rx0"), 7u);    // x held as a state variable
  EXPECT_EQ(RunAndGet(src, "chk1"), 1u);   // generator succeeds
  EXPECT_EQ(RunAndGet(src, "rx1"), 100u);  // x drawn to satisfy the constraint
}

// 18.11.1: null indicates no random variables for the call even for a randc
// variable -- it is held as a state variable, not cycled through its domain.
// The current value satisfies the constraint, so the checker returns 1 and the
// randc variable keeps its value rather than advancing to the next permutation.
TEST(InlineConstraintChecker, NullHoldsRandcVariableAsState) {
  const char* src =
      "class CA;\n"
      "  randc bit [1:0] c;\n"
      "  constraint k { c < 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.c = 2;\n"
      "    okv = a.randomize(null);\n"  // checker: c is a state variable
      "    rc = a.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);  // 2 < 3 holds
  EXPECT_EQ(RunAndGet(src, "rc"), 2u);   // not cycled: held as a state variable
}

// 18.11.1: normally, calling randomize() on a class that declares no random
// variables makes the method behave as a checker even without the null argument
// -- it assigns no value and returns only a status. Here the class has a single
// non-rand member constrained to a value; the checker evaluates the constraint
// against the member's current value. One object satisfies it (returns 1), a
// second does not (returns 0), and neither member is ever altered.
TEST(InlineConstraintChecker, NoRandomVariablesActsAsChecker) {
  const char* src =
      "class CB;\n"
      "  byte v;\n"  // no rand/randc member anywhere in the class
      "  constraint c { v == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int oka;\n"
      "  int rva;\n"
      "  int okb;\n"
      "  int rvb;\n"
      "  initial begin\n"
      "    CB a = new;\n"
      "    CB b = new;\n"
      "    a.v = 4;\n"
      "    oka = a.randomize();\n"  // no random variables -> pure checker
      "    rva = a.v;\n"
      "    b.v = 9;\n"
      "    okb = b.randomize();\n"
      "    rvb = b.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "oka"), 1u);  // 4 == 4 holds
  EXPECT_EQ(RunAndGet(src, "rva"), 4u);  // unchanged: nothing randomized
  EXPECT_EQ(RunAndGet(src, "okb"), 0u);  // 9 != 4 fails
  EXPECT_EQ(RunAndGet(src, "rvb"), 9u);  // unchanged: reports the live value
}

// 18.11.1: null designates no random variables, so EVERY class member is a
// state variable -- including a rand class-handle member. As a state variable
// the handle is held, and because it is not one of the object's active random
// variables the checker does not descend into the object it references: that
// sub-object's own random members are left untouched. Contrast the same class
// randomized without null, which is a generator and does recurse, drawing the
// sub-object's member to satisfy its constraint. Both objects run from the same
// source, so the difference is attributable solely to the null argument.
TEST(InlineConstraintChecker, NullHoldsRandObjectHandleMemberWithoutRecursing) {
  const char* src =
      "class Sub;\n"
      "  rand byte v;\n"
      "  constraint c { v == 99; }\n"
      "endclass\n"
      "class Top;\n"
      "  rand Sub s;\n"
      "  function new();\n"
      "    s = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int chk0;\n"
      "  int rv0;\n"
      "  int chk1;\n"
      "  int rv1;\n"
      "  Sub sa;\n"
      "  Sub sb;\n"
      "  initial begin\n"
      "    Top a = new;\n"
      "    Top b = new;\n"
      "    sa = a.s;\n"  // alias the sub-object handle
      "    sa.v = 7;\n"
      "    chk0 = a.randomize(null);\n"  // checker: s is state, no descent
      "    rv0 = sa.v;\n"
      "    sb = b.s;\n"
      "    sb.v = 7;\n"
      "    chk1 = b.randomize();\n"  // generator: recurses and solves v==99
      "    rv1 = sb.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "chk0"), 1u);  // Top has no constraint to fail
  EXPECT_EQ(RunAndGet(src, "rv0"), 7u);   // sub-object held: never randomized
  EXPECT_EQ(RunAndGet(src, "chk1"), 1u);  // generator solves the sub-object
  EXPECT_EQ(RunAndGet(src, "rv1"), 99u);  // sub-object drawn to satisfy v==99
}

}  // namespace
