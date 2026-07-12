#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.5.8 (global constraints) end to end. Each program
// elaborates real classes, constructs a tree of rand objects, calls
// randomize(), and copies the outcome into module variables the harness reads,
// so the behavior observed is that of parse/elaborate/run applying the rule
// through the production randomize() path (eval_randomize.cpp) rather than a
// hand-built solver state. 18.4 supplies the rand data-member and rand
// class-handle declarations the rule operates on and 18.8 supplies the
// rand_mode() state that makes a member a state variable.

// 18.5.8: when an object member of a class is declared rand, all of its
// constraints and random variables are randomized simultaneously along with the
// enclosing object's variables and constraints; a constraint expression that
// relates random variables from different objects is a global constraint. This
// models the ordered-tree example: class B holds a heap value v (inherited from
// leaf class A) and two rand subtree objects left and right, with the global
// constraints left.v <= v and right.v > v. A single randomize() of b solves b
// and both children as one whole, so both global constraints hold at once --
// which per-object sequential solving could not guarantee.
TEST(GlobalConstraint, ActiveSubtreeValuesSolvedSimultaneously) {
  const char* src =
      "class A;\n"  // leaf node
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class B extends A;\n"  // heap node
      "  rand A left;\n"
      "  rand A right;\n"
      "  constraint heapcond { left.v <= v; right.v > v; }\n"
      "  function new();\n"
      "    left = new;\n"
      "    right = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int lv;\n"
      "  int vv;\n"
      "  int rv;\n"
      "  int good;\n"
      "  initial begin\n"
      "    B b = new;\n"
      "    ok = b.randomize();\n"
      "    lv = b.left.v;\n"
      "    vv = b.v;\n"
      "    rv = b.right.v;\n"
      "    good = (ok == 1 && lv <= vv && rv > vv) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.8 rule a: the set of objects randomized as a whole is built recursively
// -- starting from the object that invoked randomize(), it reaches every rand,
// active object contained within it, and so on down the tree. Rule b then
// selects the active constraints of every object in that set. Top contains mid,
// which contains a leaf; the leaf carries its own constraint (v >= 30), mid a
// global constraint (its value exceeds the leaf's), and Top a global constraint
// (its value exceeds mid's). A single randomize() of Top solves all three
// objects at once, so the grandchild's own constraint holds (leaf.v >= 30 --
// which requires the leaf to have been reached recursively and actively solved,
// not left at its default 0) while both cross-object global constraints order
// the tree leaf.v < mid.v < top.v.
TEST(GlobalConstraint,
     RecursivelyReachedObjectsAndTheirConstraintsSolvedJointly) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] v;\n"
      "  constraint lo { v >= 30; }\n"
      "endclass\n"
      "class Mid;\n"
      "  rand bit [7:0] v;\n"
      "  rand Leaf leaf;\n"
      "  constraint mc { v > leaf.v; }\n"
      "  function new();\n"
      "    leaf = new;\n"
      "  endfunction\n"
      "endclass\n"
      "class Top;\n"
      "  rand bit [7:0] v;\n"
      "  rand Mid mid;\n"
      "  constraint tc { v > mid.v; }\n"
      "  function new();\n"
      "    mid = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int leafv;\n"
      "  int midv;\n"
      "  int topv;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Top top = new;\n"
      "    ok = top.randomize();\n"
      "    leafv = top.mid.leaf.v;\n"
      "    midv = top.mid.v;\n"
      "    topv = top.v;\n"
      "    good = (ok == 1 && leafv >= 30 && midv > leafv && topv > midv)\n"
      "           ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.8 rule c: only the active random variables are randomized; every other
// variable reference is treated as a state variable whose current value is used
// as a constant. Here the leaf value child.v is made inactive with rand_mode(0)
// (18.8) after being set to 8, so it is a state variable, while the enclosing
// node value c is still active. The global constraint child.v <= c is therefore
// solved against the fixed constant 8: child.v keeps 8 and c is drawn to
// satisfy c >= 8, proving the held value participates in the global constraint
// as a constant rather than being randomized.
TEST(GlobalConstraint, InactiveMemberIsStateConstantInGlobalConstraint) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class Node;\n"
      "  rand bit [7:0] c;\n"
      "  rand Leaf child;\n"
      "  constraint k { child.v <= c; }\n"
      "  function new();\n"
      "    child = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int cv;\n"
      "  int chv;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Node n = new;\n"
      "    Leaf lc = n.child;\n"  // alias the leaf handle
      "    lc.v = 8;\n"
      "    lc.v.rand_mode(0);\n"  // child.v held as a state constant
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    chv = lc.v;\n"
      "    good = (ok == 1 && chv == 8 && cv >= 8) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.8 rule c: because an inactive member contributes its current value as a
// binding constant rather than being randomized, a global constraint relating
// an active variable to it can become unsatisfiable. child.v is held at 0 while
// c is constrained to [5, 10], so child.v > c has no solution and randomize()
// returns 0 -- confirming the held value is a binding constant in the global
// constraint, not an ignored term. On the failed call the values are retained,
// so child.v is still its held 0.
TEST(GlobalConstraint,
     InactiveStateConstantCanMakeGlobalConstraintUnsatisfiable) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class Node;\n"
      "  rand bit [7:0] c;\n"
      "  rand Leaf child;\n"
      "  constraint k { c >= 5; c <= 10; child.v > c; }\n"
      "  function new();\n"
      "    child = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int chv;\n"
      "  initial begin\n"
      "    Node n = new;\n"
      "    Leaf lc = n.child;\n"  // alias the leaf handle
      "    lc.v = 0;\n"
      "    lc.v.rand_mode(0);\n"   // held at 0
      "    ok = n.randomize();\n"  // child.v(0) > c is impossible for c in
                                   // [5,10]
      "    chv = lc.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "chv"), 0u);
}

// 18.5.8 rule a: an object is part of the active random set only if the handle
// naming it is itself active. Here Node holds two rand leaf handles a and b;
// disabling b with rand_mode(0) (18.8) removes b's object from the set, so b is
// not randomized and its value is a state variable. The global constraint
// c >= b.v is therefore solved against b's held current value 240 (c is drawn
// >= 240), while a stays active and part of the whole. The second active object
// a is what keeps the set larger than the root, exercising the joint solve.
// Input form: a rand class-handle member made inactive at the object level
// (distinct from disabling a scalar random variable).
TEST(GlobalConstraint, InactiveObjectHandleExcludesItsObjectFromActiveSet) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class Node;\n"
      "  rand bit [7:0] c;\n"
      "  rand Leaf a;\n"
      "  rand Leaf b;\n"
      "  constraint k { c >= b.v; }\n"
      "  function new();\n"
      "    a = new;\n"
      "    b = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int cv;\n"
      "  int bv;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Node n = new;\n"
      "    Leaf lb = n.b;\n"
      "    lb.v = 240;\n"
      "    n.b.rand_mode(0);\n"  // remove object b from the active set
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    bv = lb.v;\n"
      "    good = (ok == 1 && bv == 240 && cv >= 240) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.8 rule c: a variable reference that is not one of the active random
// variables is a state variable whose current value is a constant. A plain
// (non-rand) data member is never an active random variable, so a global
// constraint that reaches it uses its current value. child.s is a non-rand
// member set to 250, and c >= child.s solves c to be at least 250 while child.s
// keeps its value. This is a different input form from a rand variable turned
// off by rand_mode(): the member is a state variable by declaration, not by
// mode.
TEST(GlobalConstraint, NonRandMemberIsStateVariableInGlobalConstraint) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] r;\n"
      "  bit [7:0] s;\n"
      "endclass\n"
      "class Node;\n"
      "  rand bit [7:0] c;\n"
      "  rand Leaf child;\n"
      "  constraint k { c >= child.s; }\n"
      "  function new();\n"
      "    child = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int cv;\n"
      "  int sv;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Node n = new;\n"
      "    Leaf lc = n.child;\n"
      "    lc.s = 250;\n"
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    sv = lc.s;\n"
      "    good = (ok == 1 && sv == 250 && cv >= 250) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5.8 rule b: only the active constraints of the active random objects are
// applied. A constraint turned off with constraint_mode(0) (18.9) is not
// active, so it is excluded and does not constrain the solve. The global
// constraint k is self-contradictory (child.v > c and c > child.v cannot both
// hold), so with k active randomize() fails (n0), but after k is disabled the
// same randomize() succeeds (n1) -- observing that the disabled constraint is
// dropped from the active set. Input form: a global constraint disabled through
// constraint_mode().
TEST(GlobalConstraint, DisabledConstraintIsExcludedFromActiveConstraints) {
  const char* src =
      "class Leaf;\n"
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class Node;\n"
      "  rand bit [7:0] c;\n"
      "  rand Leaf child;\n"
      "  constraint k { child.v > c; c > child.v; }\n"
      "  function new();\n"
      "    child = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok0;\n"
      "  int ok1;\n"
      "  initial begin\n"
      "    Node n0 = new;\n"
      "    Node n1 = new;\n"
      "    ok0 = n0.randomize();\n"     // k active -> contradictory -> fails
      "    n1.k.constraint_mode(0);\n"  // disable the global constraint
      "    ok1 = n1.randomize();\n"     // k excluded -> succeeds
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok0"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok1"), 1u);
}

}  // namespace
