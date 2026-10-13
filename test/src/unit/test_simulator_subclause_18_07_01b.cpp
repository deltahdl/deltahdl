#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.7.1: the clause's F(C obj, integer x), obj.randomize() with { x <
// local::x; }: the bare x binds to the property of C, the object being
// randomized, and local::x bypasses that class and binds to the argument,
// so over 32 draws obj.x lies from 0 below the argument 40 on every one, as
// the design test/src/e2e/local_scope_resolution.sv runs it.
TEST(LocalScopeResolutionRun, LocalBindsTheArgumentTheBareNameHides) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  function int F(C obj, integer x);\n"
      "    F = obj.randomize() with { x < local::x; x >= 0; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (32) begin\n"
      "      if (F(obj, 40) == 1) success++;\n"
      "      if (obj.x >= 0 && obj.x < 40) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.7.1: local::this binds to the scope containing the call, so in a
// Holder's method randomizing a C under x < local::this.limit the limit is
// the Holder's 12, not a member of the C the block's own this names: over
// 32 draws obj.x lies from 0 below 12 on every one.
TEST(LocalScopeResolutionRun, LocalThisIsTheCallersThis) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "class Holder;\n"
      "  rand integer x;\n"
      "  int limit = 12;\n"
      "  function int bound(C obj);\n"
      "    return obj.randomize() with { x < local::this.limit; x >= 0; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    static Holder h = new;\n"
      "    repeat (32) begin\n"
      "      if (h.bound(obj) == 1) success++;\n"
      "      if (obj.x >= 0 && obj.x < 12) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.7.1: local::x binds to the argument x of the function containing the
// call even in a relation the solver tries against values of the object's
// own x, so on every one of 4 calls the sum of x and y is the argument 9,
// not the y of 0 that x + y == x would ask for.
TEST(LocalScopeResolutionRun, LocalReachesTheArgumentPastTheTrialValues) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  function int f(C obj, int x);\n"
      "    return obj.randomize() with { x + y == local::x; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (4)\n"
      "      if (f(c, 9) == 1 && c.x + c.y == 9) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: local::x in a method of D binds to D's property x, though the C
// being randomized declares an x of its own, so on every one of 4 calls the
// C's x is D's 7.
TEST(LocalScopeResolutionRun, LocalBindsThePropertyOfTheCallersClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  bit [3:0] x = 7;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::x; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 7) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: local::super binds to the scope containing the call, so in a
// method of D, which extends B, local::super.lim is B's lim of the D
// object, 6, rather than any lim of the C being randomized or D's own: on
// every one of 4 calls the C's x is 6.
TEST(LocalScopeResolutionRun, LocalSuperIsTheCallersSuper) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  bit [3:0] lim = 1;\n"
      "endclass\n"
      "class B;\n"
      "  bit [3:0] lim = 6;\n"
      "endclass\n"
      "class D extends B;\n"
      "  bit [3:0] lim = 2;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::super.lim; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 6) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: local:: may qualify a type name, so local::nib_t is the 4-bit
// type of the module containing the call, and casting 21 to it gives 5: on
// every one of 4 calls the C's x is 5.
TEST(LocalScopeResolutionRun, LocalQualifiesTheCallersTypeName) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static int big = 21;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with { x == local::nib_t'(big); } == 1 &&\n"
      "          c.x == 5) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: given c.randomize() with, local::c binds to the scope of the
// class of c, so local::c.x is the random variable x the call solves, not
// the value c.x holds before it: on every one of 4 calls the call succeeds
// with c.x at 5.
TEST(LocalScopeResolutionRun, LocalReceiverNamesTheRandomVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with { local::c.x == 5; } == 1 && c.x == 5)\n"
      "        held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: local::lim in a method of D binds to the method's argument lim,
// which no property of D declares, so on every one of 4 calls the C's x is
// the argument 11.
TEST(LocalScopeResolutionRun, LocalBindsTheArgumentOfTheCallersMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  function int go(C c, int lim);\n"
      "    return c.randomize() with { x == local::lim; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c, 11) == 1 && c.x == 11) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// 18.7.1: local:: may qualify a type name, so in a method of D local::tri_t
// is D's 3-bit type, though the C being randomized declares a tri_t of 4
// bits, and casting 13 to it gives 5: on every one of 4 calls the C's x is 5.
TEST(LocalScopeResolutionRun, LocalQualifiesATypeOfTheCallersClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  typedef bit [3:0] tri_t;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  typedef bit [2:0] tri_t;\n"
      "  int big = 13;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::tri_t'(local::big); };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 5) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

}  // namespace
