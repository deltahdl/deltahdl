#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.7's runtime rule end to end. Each program elaborates a
// real class, calls randomize() with an inline `with { ... }` constraint block
// written in source, and copies the outcome to module variables the harness
// reads -- so the behavior observed is that of parse/elaborate/run applying the
// inline constraint, not a hand-built solver state. The wiring under test is
// the parser capturing the `with` block and the simulator applying its
// relations alongside the object's own constraints; before it, the block was
// skipped at parse time and the solve saw an empty inline set, so `with` had no
// effect.

// 18.7: the unnamed constraint_block following `with` supplies additional
// inline constraints that are applied along with the object's constraints. Here
// the object has no class constraint, so the inline `x == 42` alone pins x, and
// the randomize() call reports success.
TEST(InlineConstraintRuntime, InlineWithBlockPinsValue) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == 42; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

// 18.7: the inline constraints are applied ALONG WITH the object's own
// constraints, not in place of them. The class constraint keeps x > 40 while
// the inline block adds x < 42, leaving exactly one legal value; the solved x
// proves both were considered together.
TEST(InlineConstraintRuntime, InlineWithBlockCombinesWithClassConstraint) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x > 40; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x < 42; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 41u);
}

// 18.7: because the inline block is enforced together with the class
// constraints, an inline constraint that conflicts with a class constraint
// makes the whole solve unsatisfiable and randomize() fails (returns 0). The
// class pins x == 10 while the inline block demands x == 20.
TEST(InlineConstraintRuntime, InlineWithBlockConflictFailsSolve) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == 20; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  // The solve fails, so no value is written back and x keeps its initial 0.
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "rx"), 0u);
}

// 18.7: the constraint block following `with` can define all of the same
// constraint types and forms a class constraint can, not just simple relational
// tests. Here the inline block mixes a set-membership (inside) form with two
// relational constraints; the solver must honor all three, leaving x == 31 as
// the only member of {30,31,32} that also satisfies x > 30 and x < 32.
TEST(InlineConstraintRuntime, InlineWithBlockSupportsSetMembershipForm) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x inside {30, 31, 32}; x > 30; x < 32; "
      "};\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 31u);
}

// 18.7: the inline constraint block can reference variables local to the
// calling scope, not only the object's random variables -- this is what lets a
// caller steer randomization without mirroring local state into the class. The
// inline constraint equates the random x to the module variable `lim`, whose
// value the solver reads at call time; changing `lim` changes the pinned
// result.
TEST(InlineConstraintRuntime, InlineWithBlockReferencesCallerLocal) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int lim;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    lim = 25;\n"
      "    if (p.randomize() with { x == lim; }) rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 25u);
}

// 18.7: besides caller locals, the inline block may reference subroutine
// arguments -- the case the clause's own example uses. Here the inline
// constraint equates the random x to the function argument `y`, whose value is
// read from the live call frame at solve time, so the randomized object comes
// back pinned to the argument passed in.
TEST(InlineConstraintRuntime, InlineWithBlockReferencesSubroutineArgument) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int pin_to(int y);\n"
      "    P p;\n"
      "    int ok;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == y; };\n"
      "    return p.x;\n"
      "  endfunction\n"
      "  initial rx = pin_to(37);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 37u);
}

// 18.7: name resolution for an unrestricted inline block begins with the
// randomize() with object class, so an unqualified name that also exists in the
// calling scope binds to the object's member, not the local. Here both the
// module and class declare `x`; the inline `x < 102` constrains the object's
// random x (kept > 100 by its class constraint) rather than the module's x
// == 5. The only value satisfying both object constraints is 101, and 101 --
// not a value merely > 100 -- is the visible proof the name bound to the
// object.
TEST(InlineConstraintRuntime, InlineWithNameResolvesToObjectClassFirst) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x > 100; }\n"
      "endclass\n"
      "module t;\n"
      "  bit [7:0] x;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    int ok;\n"
      "    p = new;\n"
      "    x = 5;\n"
      "    ok = p.randomize() with { x < 102; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 101u);
}

// 18.7: "all the same constraint types and forms as a class" includes a
// distribution. An inline `x dist {42 := 1}` gives x its only weighted value,
// so the inline distribution alone pins x to 42 -- proof the dist form is
// captured from the with-block and applied, not just simple relations.
TEST(InlineConstraintRuntime, InlineWithBlockSupportsDistForm) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x dist {42 := 1}; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

// 18.7: an implication ("antecedent -> consequent") is another form a class
// constraint can take, so it is legal inline too. The class pins a to 0, so the
// antecedent holds and the inline implication forces b to 1 (b ranges over
// {0,1}); the solved b proves the inline implication was enforced.
TEST(InlineConstraintRuntime, InlineWithBlockSupportsImplicationForm) {
  const char* src =
      "class P;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { (a == 0) -> b == 1; };\n"
      "    rb = p.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

// 18.7: the if-else constraint form is likewise admitted inline. It is captured
// through a different parser path than the bare "->" implication, so it is
// exercised separately. With a pinned to 0 the guard holds and the inline
// "if (a == 0) b == 1" forces b to 1.
TEST(InlineConstraintRuntime, InlineWithBlockSupportsIfElseForm) {
  const char* src =
      "class P;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { if (a == 0) b == 1; };\n"
      "    rb = p.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

// 18.7: when the constraint block is preceded by a parenthesized
// identifier_list it is restricted -- only the listed names resolve into the
// object class; all other names resolve in the calling scope. Here both the
// object and the module declare y, and the block is restricted to (x). So `x ==
// y` binds x to the object's random x but y to the module's y (55), not the
// object's random y. The object's own y is left free. x coming back as 55 --
// the caller's y, a value the object's random y would almost never
// independently equal -- is the visible proof the unlisted name resolved in the
// calling scope.
TEST(InlineConstraintRuntime,
     RestrictedBlockResolvesUnlistedNameInCallerScope) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  bit [7:0] y;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    y = 55;\n"
      "    ok = p.randomize() with (x) { x == y; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 55u);
}

}  // namespace
