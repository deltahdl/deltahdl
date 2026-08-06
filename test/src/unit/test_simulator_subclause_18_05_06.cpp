#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the if-else constraint (18.5.6) end to end: each source
// program declares a class with an "if ( expression ) constraint_set [ else
// constraint_set ]" constraint, calls randomize() from an initial block, and
// copies the solved members out to module variables the harness can read. The
// LRM defines the if-else form to be equivalent to implications, so the
// production randomize() path captures each guarded relation as an ordinary
// "guard -> relation" and enforces it through the same Boolean-equivalent
// (!guard || relation) evaluation used for 18.5.5. The behavior observed here
// is therefore that of real elaborated source, not a hand-built solver state.
//
// The randomize() generate-and-test solver draws each variable over its whole
// domain; only the relational (inequality) constraints tighten that domain.
// Pins are written as inequality bounds so the selected value is deterministic:
// a bit variable bounded ">= 1" is fixed to 1, and "<= 0" fixes it to 0.

// 18.5.6: when the if condition is true, every constraint in the then set shall
// be satisfied and the else set imposes nothing. With mode bounded to 1 the
// condition (mode == 1) holds, so data must obey the then branch (data > 10)
// rather than the else branch (data < 5).
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

// 18.5.6: the then branch may be an unnamed constraint set grouping several
// constraints, and when the condition holds *every* constraint in that set
// shall be satisfied, not merely one. With mode bounded to 1 the condition
// holds, so both members of "{ data > 10; other < 5; }" are enforced. This
// drives the braced-set syntax through the full pipeline, observing the parser
// capturing each set member and the solver enforcing all of them together.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "    ro = o.other;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
  EXPECT_LT(RunAndGet(src, "ro"), 5u);
}

// 18.5.6: when the condition is false, every constraint in the optional else
// set shall be satisfied instead of the then set. With mode bounded to 0 the
// condition fails, so data must obey the else branch (data < 5).
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_LT(RunAndGet(src, "rd"), 5u);
}

// 18.5.6: the else branch may also be an unnamed constraint set, and when the
// condition is false every constraint in that set shall be satisfied. With mode
// bounded to 0 the condition fails, so both members of the else set
// "{ data > 10; other < 5; }" are enforced. This drives the braced-else syntax
// through the full pipeline, observing set enforcement in the else position.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "    ro = o.other;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
  EXPECT_LT(RunAndGet(src, "ro"), 5u);
}

// 18.5.6: the else part is optional. When the condition is false and no else
// set is present, the then set is not imposed. Here the then set (data > 100)
// is impossible for a 4-bit variable; because mode is bounded to 0 the
// condition fails, the then set is never imposed, and randomize() still
// succeeds. Were the then set applied regardless of the condition, the solve
// would fail.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
}

// 18.5.6: the if condition can be any integral expression, not just an equality
// test. A relational predicate ("mode > 5") selects the branch; with mode
// bounded into 10..15 the condition holds, so the then set (data > 10) applies.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

// 18.5.6: the condition may be any integral expression, including a bare
// variable taken for its truth value rather than a comparison. With flag
// bounded to 1 (nonzero, so the condition is true) the then set (data > 10)
// applies rather than the else set. This exercises the bare-truthiness
// condition form.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

// 18.5.6: the condition and the guarded set are interdependent and constrain
// each other. Here mode is left free over {0, 1} but data is bounded to 15, a
// value the then set (data < 10) forbids. The then set can only be escaped by
// making the condition false, so the guarded set drives mode away from 1.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rm = o.mode;\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rm"), 0u);
  EXPECT_EQ(RunAndGet(src, "rd"), 15u);
}

// 18.5.6: an "else if" chain is an if-else whose else set is itself another
// if-else, so the matching branch governs. With mode bounded to 2 the outer
// test (mode == 1) fails and the inner test (mode == 2) holds, so data must
// obey the inner then set (data > 100).
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 100u);
}

// 18.5.6: when the condition is forced true and the then set cannot be
// satisfied, no assignment obeys the if constraint and randomize() shall fail.
// mode is bounded to 1 (condition true) and the then set (data > 100) is
// impossible for a 4-bit variable, with no else branch to escape to.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.6: symmetrically, when the condition is forced false the else set shall
// be satisfied, so an unsatisfiable else set makes randomize() fail. mode is
// bounded to 0 (condition false), and the else set (data > 100) is impossible
// for a 4-bit variable; the condition cannot be made true to escape it, so no
// assignment obeys the constraint.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.6: an else omitted from a nested if sequence binds to the closest
// preceding if that lacks one. Here the else belongs to the inner "if (b ==
// 1)", so with a bounded to 1 and b bounded to 0 the outer condition holds, the
// inner condition fails, and the inner else set (data > 10) applies. Had the
// else been (incorrectly) bound to the outer if, the outer condition being true
// would leave data unconstrained.
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
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rd = o.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rd"), 10u);
}

}  // namespace
