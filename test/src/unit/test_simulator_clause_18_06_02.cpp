#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.6.2: every class contains pre_randomize() and post_randomize() methods.
// A class that does not override them has built-in versions whose processing
// is empty, so randomization proceeds and produces a value exactly as if they
// were absent. The solver models "not overridden" as having no pre/post hook
// registered; with neither hook set, Solve() still randomizes successfully and
// the default built-ins contribute no processing of their own.
TEST(PrePostRandomize, DefaultBuiltinsAreNoOpsWhenNotOverridden) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  // No SetPreRandomize/SetPostRandomize: the default built-in methods apply.
  ASSERT_TRUE(solver.Solve());

  // The random variable was still computed and assigned a value in range.
  ASSERT_EQ(solver.GetValues().size(), 1u);
  const int64_t kX = solver.GetValues().at("x");
  EXPECT_GE(kX, 0);
  EXPECT_LE(kX, 100);
}

// 18.6.2: a single randomize() first invokes pre_randomize() and then, after
// the values are computed, invokes post_randomize(). Beyond the compute
// boundary, this fixes both the relative order of the two methods and their
// cardinality: across one Solve() each hook fires exactly once, with
// pre_randomize() strictly preceding post_randomize(). Recording an ordered
// log from the solver's pre/post hook sites observes that sequence directly.
TEST(PrePostRandomize, PreThenPostInvokedExactlyOnceInOrder) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  std::vector<std::string> events;
  solver.SetPreRandomize([&]() { events.push_back("pre"); });
  solver.SetPostRandomize([&]() { events.push_back("post"); });

  ASSERT_TRUE(solver.Solve());

  // pre fired once, then post fired once — no extra or missing invocations.
  const std::vector<std::string> kExpected = {"pre", "post"};
  EXPECT_EQ(events, kExpected);
}

// 18.6.2: randomize() invokes pre_randomize() first — before any new random
// value is computed — and post_randomize() after the new values are computed
// AND assigned. Observed through the real randomize() path from source: a user
// pre_randomize() records the random member as it stands before the solve (its
// default 0), while a user post_randomize() records the same member after the
// solve, when the newly drawn value has already been written back onto the
// object (42). Seeing 0 at pre and 42 at post fixes both the pre-before-compute
// order and the "after computed and assigned" timing of post_randomize.
TEST(PrePostRandomizeFromSource, PreObservesDefaultPostObservesAssignedValue) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  int pre_saw;\n"
      "  int post_saw;\n"
      "  constraint c { v == 42; }\n"
      "  function void pre_randomize();\n"
      "    pre_saw = v;\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "    post_saw = v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.pre_saw == 0 && o.post_saw == 42) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: pre_randomize() and post_randomize() are not virtual, but because
// they are called by the virtual randomize() they appear to behave as virtual
// methods. Randomizing through a base-class handle bound to a derived object
// dispatches post_randomize() to the derived override, not the base version:
// the derived post_randomize() stamps the tag with its own marker (2), so
// reading tag == 2 confirms the dynamic-type dispatch. Input form: the call
// resolved through a base-class handle.
TEST(PrePostRandomizeFromSource, PostRandomizeAppearsVirtualThroughBaseHandle) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int tag;\n"
      "  constraint cb { v == 1; }\n"
      "  function void post_randomize();\n"
      "    tag = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function void post_randomize();\n"
      "    tag = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Base bh;\n"
      "  Derived dh;\n"
      "  initial begin\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.tag == 2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: when a derived class does not itself define pre_randomize(), the
// pre_randomize() invoked by randomize() automatically reaches the inherited
// (super) implementation. A derived object whose class declares no
// pre_randomize() is randomized; the base-class pre_randomize() still runs and
// leaves its marker (7) on the object, alongside the derived-only and inherited
// random variables both being solved. Input form: a derived class with no user
// pre_randomize() override.
TEST(PrePostRandomizeFromSource, InheritedPreRandomizeRunsForDerivedObject) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_pre;\n"
      "  constraint cb { v == 3; }\n"
      "  function void pre_randomize();\n"
      "    base_pre = 7;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int w;\n"
      "  constraint cw { w == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_pre == 7 && d.v == 3 && d.w == 4) ? 1 : "
      "0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: randomize() invokes post_randomize() on the object AND on all of its
// random object members. An outer object holds a rand class-handle member; a
// single randomize() on the outer object drives the inner object's
// post_randomize(), which reads the inner random member after it has been
// solved and assigned (9) — so the inner post_randomize() both ran and saw the
// new value. Input form: a rand class-handle member (a random sub-object) with
// its own post_randomize().
TEST(PrePostRandomizeFromSource, PostRandomizeRunsOnRandObjectMember) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  int inner_post;\n"
      "  constraint cx { x == 9; }\n"
      "  function void post_randomize();\n"
      "    inner_post = x;\n"
      "  endfunction\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    good = (ok == 1 && ih.inner_post == 9) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: randomize() invokes pre_randomize() on the object AND on all of its
// random object members — the companion of the post_randomize()-on-member rule.
// A single randomize() on the outer object drives the inner (rand class-handle)
// member's pre_randomize(), which stamps its own marker (5); reading it back
// through the outer object's handle confirms the inner pre_randomize() ran as
// part of the enclosing call. Input form: a rand class-handle member (a random
// sub-object) with its own pre_randomize().
TEST(PrePostRandomizeFromSource, PreRandomizeRunsOnRandObjectMember) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  int inner_pre;\n"
      "  constraint cx { x == 9; }\n"
      "  function void pre_randomize();\n"
      "    inner_pre = 5;\n"
      "  endfunction\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    good = (ok == 1 && ih.inner_pre == 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: an overridden pre_randomize()/post_randomize() shall call its
// associated base-class method to keep the base's processing step; when it does
// (through super), both the base and the derived processing run. A derived
// post_randomize() that first calls super.post_randomize() causes the base
// post_randomize() to leave its marker (base_ran) as well as the derived one
// (deriv_ran). Contrast the appears-virtual test above, where an override that
// does NOT call super leaves the base step skipped — together the two fix both
// halves of the rule. Input form: a derived override that chains to super.
TEST(PrePostRandomizeFromSource, OverrideChainsToBaseThroughSuper) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_ran;\n"
      "  constraint c { v == 1; }\n"
      "  function void post_randomize();\n"
      "    base_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int deriv_ran;\n"
      "  function void post_randomize();\n"
      "    super.post_randomize();\n"
      "    deriv_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_ran == 1 && d.deriv_ran == 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: the companion of the inherited-pre_randomize rule for post_randomize.
// When a derived class defines no post_randomize() of its own, the
// post_randomize() invoked by randomize() automatically reaches the inherited
// (super) implementation. A derived object whose class declares no
// post_randomize() is randomized; the base-class post_randomize() still runs
// and, because it fires after the write-back, records the derived object's
// just-assigned random member (3), while the derived-only variable is solved to
// 4. Input form: a derived class with no user post_randomize() override
// (post-invocation path, distinct from the pre-hook path).
TEST(PrePostRandomizeFromSource, InheritedPostRandomizeRunsForDerivedObject) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_post;\n"
      "  constraint cb { v == 3; }\n"
      "  function void post_randomize();\n"
      "    base_post = v;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int w;\n"
      "  constraint cw { w == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_post == 3 && d.w == 4) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: pre_randomize() is not virtual but appears to behave virtually
// because it is called by the virtual randomize() — the companion of the
// post_randomize apparent-virtual rule. Randomizing through a base-class handle
// bound to a derived object dispatches pre_randomize() to the derived override
// (marker 2), not the base version (marker 1), so reading tag == 2 confirms
// dynamic-type dispatch on the pre-hook path. Input form: the call resolved
// through a base-class handle (pre-hook path).
TEST(PrePostRandomizeFromSource, PreRandomizeAppearsVirtualThroughBaseHandle) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int tag;\n"
      "  constraint cb { v == 1; }\n"
      "  function void pre_randomize();\n"
      "    tag = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function void pre_randomize();\n"
      "    tag = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Base bh;\n"
      "  Derived dh;\n"
      "  initial begin\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.tag == 2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.2: the super-chaining rule applied to pre_randomize() — the companion of
// the post_randomize super-chain test. A derived pre_randomize() that first
// calls super.pre_randomize() keeps the base's pre-randomization step: the base
// pre_randomize() leaves its marker (base_ran) as well as the derived one
// (deriv_ran). Contrast the pre appears-virtual test above, whose override does
// NOT call super and leaves the base step skipped. Input form: a derived
// pre_randomize() override that chains to super (pre-hook path).
TEST(PrePostRandomizeFromSource, PreOverrideChainsToBaseThroughSuper) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_ran;\n"
      "  constraint c { v == 1; }\n"
      "  function void pre_randomize();\n"
      "    base_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int deriv_ran;\n"
      "  function void pre_randomize();\n"
      "    super.pre_randomize();\n"
      "    deriv_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_ran == 1 && d.deriv_ran == 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
