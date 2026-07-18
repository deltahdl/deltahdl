#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// 18.6.3: random variables declared static are shared by all instances of the
// class in which they are declared, and each randomize() changes the variable
// in every class instance. Built from real source: a class declares `static
// rand bit [7:0] x` constrained to a small domain, and two instances are
// constructed. The shared cell is first seeded with a sentinel out of the
// constraint domain; randomizing one instance draws a fresh in-domain value and
// publishes it to the single class-wide storage, so the other instance observes
// exactly that value too. Driven through the full pipeline, this observes the
// production randomize path writing the drawn value to the shared static cell
// rather than to a private per-object copy.
TEST(BehaviorOfRandomizationMethods, StaticRandSharedAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static rand bit [7:0] x;\n"
      "  constraint dom { x > 0; x < 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int va, vb, ok;\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    a.x = 200;\n"           // sentinel outside the constraint domain
      "    ok = a.randomize();\n"  // draws x in (0,50), writes the shared cell
      "    va = a.x;\n"
      "    vb = b.x;\n"  // the other instance sees the same new value
      "    good = (ok == 1 && va == vb && va > 0 && va < 50) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.3 (same rule, randc operand): the "declared static" random variable the
// rule shares across instances can be cyclic (randc), not only plain rand. A
// class declares `static randc bit [1:0] x` and two instances are constructed.
// Each instance is randomized in turn; both handles observe the value the most
// recent randomize() produced (the shared cell), so the two reads taken after
// each call agree. Because the cyclic state is shared too, the two successive
// draws differ — which also proves the second handle's randomize() changed the
// value the first handle now reads, rather than each keeping a private copy.
TEST(BehaviorOfRandomizationMethods, StaticRandcSharedAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static randc bit [1:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int va0, vb0, va1, vb1, ok;\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    ok = a.randomize();\n"  // draw #1, written to the shared cell
      "    va0 = a.x;\n"
      "    vb0 = b.x;\n"           // the other instance sees draw #1 too
      "    ok = b.randomize();\n"  // draw #2 redraws the shared cell
      "    va1 = a.x;\n"           // the first instance now sees draw #2
      "    vb1 = b.x;\n"
      "    good = (va0 == vb0 && va1 == vb1 && va0 != va1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.3: if randomize() fails, the constraints are infeasible and the random
// variables retain their previous values. Built from real source: a class holds
// an infeasible constraint set (one variable pinned to two different values at
// once), the variable is first given a known value, and the failing randomize()
// must leave that value in place. The return status is 0 (18.6.1) and the
// variable still holds the value it had before the call.
TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsPreviousValue) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bad { x == 10; x == 20; }\n"  // infeasible
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int val;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.x = 42;\n"            // previous value
      "    ok = c.randomize();\n"  // fails: constraints infeasible
      "    val = c.x;\n"           // must still be 42
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "val"), 42u);
}

// 18.6.3 (edge of the retain rule, multiple variables): a failed randomize()
// restores *every* random variable, not only the one the infeasible constraint
// names. Two random variables are given known values; the constraint set is
// made infeasible through the first; after the failing call both variables
// retain the values they had before, rather than any partial draw the failed
// search made.
TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsAllPreviousValues) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] a;\n"
      "  rand bit [7:0] b;\n"
      "  constraint bad { a == 1; a == 2; }\n"  // infeasible via 'a'; 'b' free
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int va;\n"
      "  int vb;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.a = 11;\n"
      "    c.b = 22;\n"
      "    ok = c.randomize();\n"  // fails on 'a'
      "    va = c.a;\n"
      "    vb = c.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "va"), 11u);
  EXPECT_EQ(RunAndGet(src, "vb"), 22u);
}

// 18.6.3 (edge combining static sharing with the retain rule): a failed
// randomize() leaves the shared static cell unchanged for every instance. One
// handle seeds the shared static variable; a randomize() through another handle
// fails on infeasible constraints; because a failed call retains the previous
// value, every instance still observes the seeded value afterward.
TEST(BehaviorOfRandomizationMethods,
     FailedRandomizeLeavesSharedStaticUnchanged) {
  const char* src =
      "class C;\n"
      "  static rand bit [7:0] x;\n"
      "  constraint bad { x == 10; x == 20; }\n"  // infeasible
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int va;\n"
      "  int vb;\n"
      "  initial begin\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    a.x = 7;\n"             // shared cell = 7 for every instance
      "    ok = b.randomize();\n"  // fails: constraints infeasible
      "    va = a.x;\n"            // both still read 7
      "    vb = b.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "va"), 7u);
  EXPECT_EQ(RunAndGet(src, "vb"), 7u);
}

// 18.6.3: if randomize() fails, post_randomize() is not called. Built from real
// source: a class defines a post_randomize() that counts its own invocations
// and holds an infeasible constraint set. After the failing randomize(), the
// counter is still zero — the post hook did not run.
TEST(BehaviorOfRandomizationMethods, PostRandomizeNotCalledOnFailure) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int posts;\n"
      "  constraint bad { x == 10; x == 20; }\n"  // infeasible
      "  function void post_randomize(); posts = posts + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int posts_after;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    ok = c.randomize();\n"  // fails
      "    posts_after = c.posts;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "posts_after"), 0u);
}

// 18.6.3 (companion to the rule above): the same post_randomize() *is* called
// on a successful randomize(), so its absence on failure is the rule at work
// rather than a hook that never fires. The class is identical except its
// constraints are feasible; the counter reaches one after the call.
TEST(BehaviorOfRandomizationMethods, PostRandomizeCalledOnSuccess) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int posts;\n"
      "  constraint ok_c { x < 50; }\n"  // feasible
      "  function void post_randomize(); posts = posts + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int posts_after;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    ok = c.randomize();\n"  // succeeds
      "    posts_after = c.posts;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "posts_after"), 1u);
}

// 18.6.3: randomize() implements object random stability — its draws come from
// the object's own RNG, so they are reproducible from that object's seed. An
// object's RNG is seeded by its srandom() method (18.13.3). Two objects of the
// same class seeded to the same value produce the same first draw, observed end
// to end through real srandom() and randomize() calls.
TEST(BehaviorOfRandomizationMethods,
     ObjectRandomStabilityReproducibleFromSeed) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int same;\n"
      "  initial begin\n"
      "    int oka, okb;\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    a.srandom(100);\n"
      "    oka = a.randomize();\n"
      "    b.srandom(100);\n"
      "    okb = b.randomize();\n"
      "    same = (oka == 1 && okb == 1 && a.x == b.x) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
