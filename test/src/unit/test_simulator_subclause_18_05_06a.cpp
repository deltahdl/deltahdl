#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstraintIfElse, ThenBranchAppliedWhenConditionTrue) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode >= 1; }\n"
      "  constraint c { if (mode == 1) data > 10; else data < 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

TEST(ConstraintIfElse, BracedThenSetAllConstraintsEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  rand bit [3:0] other;\n"
      "  constraint fm { mode >= 1; }\n"
      "  constraint c { if (mode == 1) { data > 10; other < 5; } }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  int ro;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "    ro = o.other;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
  EXPECT_LT(RunAndGet(src, "ro"), 5u);
}

TEST(ConstraintIfElse, ElseBranchAppliedWhenConditionFalse) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode <= 0; }\n"
      "  constraint c { if (mode == 1) data > 10; else data < 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_LT(RunAndGet(src, "rd"), 5u);
}

TEST(ConstraintIfElse, BracedElseSetAllConstraintsEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  rand bit [3:0] other;\n"
      "  constraint fm { mode <= 0; }\n"
      "  constraint c { if (mode == 1) data < 2;\n"
      "                 else { data > 10; other < 5; } }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  int ro;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "    ro = o.other;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
  EXPECT_LT(RunAndGet(src, "ro"), 5u);
}

TEST(ConstraintIfElse, AbsentElseImposesNothing) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode <= 0; }\n"
      "  constraint c { if (mode == 1) data > 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
}

TEST(ConstraintIfElse, ConditionMayBeArbitraryExpression) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode >= 10; }\n"
      "  constraint c { if (mode > 5) data > 10; else data < 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

TEST(ConstraintIfElse, BareVariableConditionSelectsBranch) {
  const char* src =
      "class C;\n"
      "  rand bit flag;\n"
      "  rand bit [3:0] data;\n"
      "  constraint ff { flag >= 1; }\n"
      "  constraint c { if (flag) data > 10; else data < 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

TEST(ConstraintIfElse, GuardedSetConstrainsCondition) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fd { data >= 15; }\n"
      "  constraint c { if (mode == 1) data < 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rm;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rm = o.mode;\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rm"), 0u);
  EXPECT_EQ(RunAndGet(src, "rd"), 15u);
}

TEST(ConstraintIfElse, ElseIfChainSelectsMatchingBranch) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] data;\n"
      "  constraint fm { mode >= 2; mode <= 2; }\n"
      "  constraint c { if (mode == 1) data < 10;\n"
      "                 else if (mode == 2) data > 100;\n"
      "                 else data == 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 100u);
}

TEST(ConstraintIfElse, UnsatisfiableThenSetUnderForcedConditionFails) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode >= 1; }\n"
      "  constraint c { if (mode == 1) data > 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

TEST(ConstraintIfElse, UnsatisfiableElseSetUnderForcedConditionFails) {
  const char* src =
      "class C;\n"
      "  rand bit mode;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fm { mode <= 0; }\n"
      "  constraint c { if (mode == 1) data < 2; else data > 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

TEST(ConstraintIfElse, DanglingElseBindsToInnerIf) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit [3:0] data;\n"
      "  constraint fa { a >= 1; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint c { if (a == 1) if (b == 1) data < 5; else data > 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

}  // namespace
