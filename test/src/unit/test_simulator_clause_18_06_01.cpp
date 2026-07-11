#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// 18.6.1: randomize() returns 1 when it successfully sets every active random
// variable to a valid value. A single random variable (declared with §18.4
// rand) constrained (§18.5) to a domain is randomized through the real
// randomize() method; the call reports 1 and the assigned value lies inside the
// declared domain. Driven from source through the full pipeline so the return
// value and the write-back both come from the production randomize() path.
TEST(RandomizeMethod, ReturnsOneAndAssignsValidValue) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint rng { v >= 10; v <= 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    ok = c.randomize();\n"
      "    good = (ok == 1 && c.v >= 10 && c.v <= 20) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: randomize() generates the random variable's value subject to the
// active constraints -- the constraint, not chance, dictates the result. A
// single random variable pinned by an equality constraint is randomized through
// the real randomize() method: the call returns 1 and the variable holds
// exactly the value the active constraint requires, observed after driving real
// new() and randomize() through the full pipeline.
TEST(RandomizeMethod, RandomizesInstanceSubjectToConstraint) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint c { v == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C p = new;\n"
      "    ok = p.randomize();\n"
      "    good = (ok == 1 && p.v == 42) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: otherwise randomize() returns 0. When the active constraints cannot
// all be satisfied -- here the same random variable is pinned to two different
// values -- the solve fails and the method returns 0. Built from real source so
// the returned status is the one produced by the production randomize() path.
TEST(RandomizeMethod, ReturnsZeroWhenUnsatisfiable) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint bad { v == 10; v == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    ok = c.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.6.1: randomize() generates values for ALL the active random variables in
// the object, not merely the ones a single constraint happens to mention. Three
// independent random variables are each constrained to a distinct disjoint
// domain; a successful call returns 1 and every one of them lands inside its
// own range, showing each active variable was randomized.
TEST(RandomizeMethod, AssignsEveryActiveVariable) {
  const char* src =
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint r {\n"
      "    a >= 0; a <= 5;\n"
      "    b >= 10; b <= 20;\n"
      "    c >= 100; c <= 110;\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 &&\n"
      "            o.a >= 0 && o.a <= 5 &&\n"
      "            o.b >= 10 && o.b <= 20 &&\n"
      "            o.c >= 100 && o.c <= 110) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: randomize() sets each active random variable to a value valid for its
// declared type. A packed-vector random variable (a §18.4 rand member narrower
// than the default word) is randomized with no constraint; the call returns 1
// and the drawn value fits the declared 4-bit width, so it is valid for the
// variable's type. Input form: a packed-vector rand member rather than a plain
// int.
TEST(RandomizeMethod, RandomizesPackedVectorMemberWithinType) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] nib;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.nib <= 15) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: the same obligation for the narrowest integral type -- a single-bit
// random variable. Randomizing it returns 1 and leaves it holding a value valid
// for a 1-bit type (0 or 1). Input form: a single-bit rand member.
TEST(RandomizeMethod, RandomizesSingleBitMember) {
  const char* src =
      "class C;\n"
      "  rand bit flag;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.flag <= 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: an active random variable declared with the §18.4 randc
// (random-cyclic) modifier is also randomized by randomize() subject to the
// active constraints. Driving a real randc declaration through the full
// pipeline, a constraint pins the variable to a single value; the call returns
// 1 and the variable holds that value -- randomize() handles the randc form,
// not just plain rand. Input form: a randc §18.4 declaration.
TEST(RandomizeMethod, RandomizesRandcVariable) {
  const char* src =
      "class C;\n"
      "  randc bit [3:0] v;\n"
      "  constraint c { v == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.v == 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: randomize() is a virtual method, so a call through a superclass
// handle is dispatched to the dynamic object and randomizes that object's full
// set of active random variables -- including a random variable declared only
// in the derived class, which the static (base) type does not know. Both the
// inherited base variable and the derived-only variable are set, confirming the
// call bound to the dynamic type. Input form: the call resolved through a
// base-class handle.
TEST(RandomizeMethod, RandomizeIsVirtualDispatchedToDynamicType) {
  const char* src =
      "class Base;\n"
      "  rand int b;\n"
      "  constraint cb { b == 5; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int d;\n"
      "  constraint cd { d == 9; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Base bh;\n"
      "    Derived dh;\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.b == 5 && dh.d == 9) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: randomize() is a class method callable on the current object from
// inside another method through the this handle. A class method invokes
// this.randomize(); the returned status flows back as the method's int result
// and the constrained variable is set. Input form: the call in this.-prefixed
// position inside a class method rather than on an external handle.
TEST(RandomizeMethod, RandomizeInvokedThroughThisInMethod) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint c { v == 7; }\n"
      "  function int run();\n"
      "    return this.randomize();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.run();\n"
      "    good = (ok == 1 && o.v == 7) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.6.1: randomize() sets all the random variables AND objects to valid
// values. A rand object-handle member names a sub-object whose own random
// members must also be randomized by the enclosing call. The outer object
// constructs its rand inner object in new(); randomizing the outer object
// returns 1 and, without any separate call on the inner handle, the inner
// object's constrained random member is set -- so randomize() recursed into the
// referenced object. Input form: a rand class-handle member (a random
// sub-object).
TEST(RandomizeMethod, RandomizesReferencedRandObject) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  constraint cx { x == 13; }\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    rx = ih.x;\n"
      "    good = (ok == 1 && rx == 13) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
