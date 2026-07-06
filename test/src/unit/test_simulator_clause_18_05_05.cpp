#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive the implication constraint (18.5.5) end to end: each source
// program declares a class with an "expression -> constraint_set" constraint,
// calls randomize() from an initial block, and copies the solved members out to
// module variables the harness can read. The implication is enforced by the
// production randomize() path — the "->" operator is evaluated by the ordinary
// expression evaluator, which computes the Boolean equivalent !a || b — so the
// behavior observed here is that of real elaborated source, not a hand-built
// solver state.
//
// The randomize() generate-and-test solver draws each variable over its whole
// domain; only the relational (inequality) constraints tighten that domain.
// Every pin below is therefore written as an inequality bound so the solved
// value is deterministic: "v <= k" (with v's natural lower bound 0) fixes v to
// [0, k], and a matching lower bound narrows it to a single value.

// 18.5.5: when the antecedent of "a -> b" holds, every constraint in the
// consequent shall be satisfied. Member 'a' is bounded to 0, so the antecedent
// (a == 0) always holds; 'b' ranges over {0, 1}, so the only draw the
// implication accepts is the one obeying the consequent b == 1.
TEST(ConstraintImplication, ConsequentEnforcedWhenAntecedentTrue) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

// 18.5.5: if the antecedent is false the generated values are unconstrained, so
// the consequent imposes nothing. 'a' is bounded to 1, making (a == 0) false,
// while 'b' is bounded to 0 — a value the consequent b == 1 would forbid were
// it enforced. The solve still succeeds and leaves b at 0.
TEST(ConstraintImplication, ConsequentIgnoredWhenAntecedentFalse) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a >= 1; a <= 1; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 0u);
}

// 18.5.5: when the antecedent holds, *all* of the constraints in the consequent
// shall be satisfied, not merely one. The consequent here is a conjunctive
// constraint expression, so with 'a' bounded to 0 (antecedent true) the solved
// values must obey both b == 1 and c == 1.
TEST(ConstraintImplication, AllConsequentConditionsEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit c;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint fc { c <= 1; }\n"
      "  constraint impl { (a == 0) -> (b == 1 && c == 1); }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc"), 1u);
}

// 18.5.5: the consequent may be an unnamed constraint set — a brace-enclosed
// group of constraint expressions — and when the antecedent holds every
// constraint in that set shall be satisfied. With 'a' bounded to 0 the
// antecedent holds, so both members of the set "{ b == 1; c == 1; }" are
// enforced. This drives the braced-set syntax through the full pipeline, so it
// observes the parser capturing the set and the solver enforcing each member.
TEST(ConstraintImplication, BracedConsequentSetEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit c;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint fc { c <= 1; }\n"
      "  constraint impl { (a == 0) -> { b == 1; c == 1; } }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc"), 1u);
}

// 18.5.5: the consequent constraint_set may be any valid constraint, not only
// an equality. Here the consequent is a relational (inequality) constraint:
// with 'a' bounded to 0 the antecedent holds, so the solved 'b' must satisfy b
// > 5.
TEST(ConstraintImplication, ConsequentMayBeInequalityConstraint) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit [2:0] b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 7; }\n"
      "  constraint impl { (a == 0) -> b > 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rb"), 5u);
}

// 18.5.5: the antecedent may be any integral expression, including a bare
// variable taken for its truth value rather than a comparison. Member 'm' is
// bounded to 2 (nonzero, so the antecedent is true), which drives the
// consequent b == 1.
TEST(ConstraintImplication, BareVariableAntecedent) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] m;\n"
      "  rand bit b;\n"
      "  constraint fm { m >= 2; m <= 2; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint impl { m -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

// 18.5.5: a -> b is Boolean-equivalent to (!a || b), and the two sides are
// interdependent — conversely, if the consequent cannot be satisfied then the
// antecedent shall be false. 'b' is bounded to 0, making the consequent b == 1
// unsatisfiable, so the only way to satisfy the implication is for (a == 0) to
// be false; the solver must therefore drive 'a' (free over {0, 1}) to 1. This
// exercises the contrapositive direction.
TEST(ConstraintImplication, AntecedentDrivenFalseByUnsatisfiableConsequent) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 1; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int ra;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    ra = o.a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 1u);
}

// 18.5.5: the antecedent may be any integral expression, not only an equality.
// A general predicate antecedent ("a > 1") drives the consequent: with 'a'
// bounded to 2 the antecedent holds, so 'b' (free over 0..3) must equal 3.
TEST(ConstraintImplication, GeneralIntegralAntecedent) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  rand bit [1:0] b;\n"
      "  constraint fa { a >= 2; a <= 2; }\n"
      "  constraint fb { b <= 3; }\n"
      "  constraint impl { (a > 1) -> b == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 3u);
}

// 18.5.5: because a -> b is equivalent to (!a || b), when the antecedent is
// forced true and the consequent cannot be met the implication is
// unsatisfiable, so randomize() shall fail rather than hand back a value that
// breaks the rule. 'a' is bounded to 0 (antecedent true) while 'b' is bounded
// to 0, so the consequent b == 1 can never hold.
TEST(ConstraintImplication, RandomizeFailsWhenForcedAntecedentImpossible) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
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

}  // namespace
