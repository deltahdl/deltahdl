#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(GlobalConstraint, ActiveSubtreeValuesSolvedSimultaneously) {
  const char* src =
      "class A;\n"
      "  rand bit [7:0] v;\n"
      "endclass\n"
      "class B extends A;\n"
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
      "    static B b = new;\n"
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
      "    static Top top = new;\n"
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
      "    static Node n = new;\n"
      "    static Leaf lc = n.child;\n"
      "    lc.v = 8;\n"
      "    lc.v.rand_mode(0);\n"
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    chv = lc.v;\n"
      "    good = (ok == 1 && chv == 8 && cv >= 8) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static Node n = new;\n"
      "    static Leaf lc = n.child;\n"
      "    lc.v = 0;\n"
      "    lc.v.rand_mode(0);\n"
      "    ok = n.randomize();\n"
      "    chv = lc.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "chv"), 0u);
}

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
      "    static Node n = new;\n"
      "    static Leaf lb = n.b;\n"
      "    lb.v = 240;\n"
      "    n.b.rand_mode(0);\n"
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    bv = lb.v;\n"
      "    good = (ok == 1 && bv == 240 && cv >= 240) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static Node n = new;\n"
      "    static Leaf lc = n.child;\n"
      "    lc.s = 250;\n"
      "    ok = n.randomize();\n"
      "    cv = n.c;\n"
      "    sv = lc.s;\n"
      "    good = (ok == 1 && sv == 250 && cv >= 250) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

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
      "    static Node n0 = new;\n"
      "    static Node n1 = new;\n"
      "    ok0 = n0.randomize();\n"
      "    n1.k.constraint_mode(0);\n"
      "    ok1 = n1.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok0"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok1"), 1u);
}

}  // namespace
