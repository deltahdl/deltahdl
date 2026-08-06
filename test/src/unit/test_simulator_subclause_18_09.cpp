#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.9's runtime rule end to end. Each program elaborates
// a real class with named constraint blocks, calls constraint_mode() from
// source, and copies the outcome to module variables the harness reads -- so
// the behavior observed is that of parse/elaborate/run applying the rule, not a
// hand-built solver state. Two mutually conflicting equality constraints on one
// variable make randomize() unsatisfiable while both are active; turning one
// OFF removes it from the solve so the survivor pins the variable and the call
// succeeds. That flip is the visible proof that constraint_mode() controls
// whether a block is considered.

// 18.9 / Table 18-4: a void-form constraint_mode(0) call sets the named block
// inactive, so randomize() no longer enforces it. With both pins active the
// solve is unsatisfiable (returns 0); disabling one leaves the other binding
// and the solve succeeds with the surviving pin's value.
TEST(ConstraintModeRuntime, VoidOffRemovesBlockFromSolve) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c_lo { x == 10; }\n"
      "  constraint c_hi { x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_both;\n"
      "  int ok_one;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok_both = p.randomize();\n"
      "    p.c_hi.constraint_mode(0);\n"
      "    ok_one = p.randomize();\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_both"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_one"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 10u);
}

// 18.9: constraint_mode(1) sets a previously disabled block active again, so
// randomize() enforces it once more. Toggling c_hi off then on restores the
// original conflict, and the solve is unsatisfiable again.
TEST(ConstraintModeRuntime, VoidOnReenablesBlock) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c_lo { x == 10; }\n"
      "  constraint c_hi { x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_off;\n"
      "  int ok_on;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    p.c_hi.constraint_mode(0);\n"
      "    ok_off = p.randomize();\n"
      "    p.c_hi.constraint_mode(1);\n"
      "    ok_on = p.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_off"), 1u);
  EXPECT_EQ(RunAndGet(src, "ok_on"), 0u);
}

// 18.9: the nonvoid form returns the current active state -- 1 for an active
// block and 0 after it was turned off. A block is active when the object is
// created, so the query reads 1 before any change and 0 after
// constraint_mode(0).
TEST(ConstraintModeRuntime, NonvoidReturnsActiveState) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int st_before;\n"
      "  int st_after;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    st_before = p.c.constraint_mode();\n"
      "    p.c.constraint_mode(0);\n"
      "    st_after = p.c.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "st_before"), 1u);
  EXPECT_EQ(RunAndGet(src, "st_after"), 0u);
}

// 18.9: called as a void function with no constraint identifier, the operation
// applies to all constraints within the object. Disabling every block removes
// the conflict, so randomize() succeeds, and querying each block confirms both
// are inactive.
TEST(ConstraintModeRuntime, UnnamedFormDisablesAllBlocks) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c_lo { x == 10; }\n"
      "  constraint c_hi { x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int q_lo;\n"
      "  int q_hi;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    p.constraint_mode(0);\n"
      "    ok = p.randomize();\n"
      "    q_lo = p.c_lo.constraint_mode();\n"
      "    q_hi = p.c_hi.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "q_lo"), 0u);
  EXPECT_EQ(RunAndGet(src, "q_hi"), 0u);
}

// 18.9: the named constraint can be any constraint block in the class
// hierarchy, including one inherited from a base class. Disabling the base
// block through a derived handle removes the base pin, so the derived pin binds
// the solve; the query on the base block confirms it is inactive.
TEST(ConstraintModeRuntime, NamedFormReachesInheritedBlock) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bc { x == 7; }\n"
      "endclass\n"
      "class Der extends Base;\n"
      "  constraint dc { x == 9; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_both;\n"
      "  int ok_one;\n"
      "  int rx;\n"
      "  int q_base;\n"
      "  initial begin\n"
      "    Der d;\n"
      "    d = new;\n"
      "    ok_both = d.randomize();\n"
      "    d.bc.constraint_mode(0);\n"
      "    ok_one = d.randomize();\n"
      "    rx = d.x;\n"
      "    q_base = d.bc.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_both"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_one"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 9u);
  EXPECT_EQ(RunAndGet(src, "q_base"), 0u);
}

// 18.9: the nonvoid form returns the block's active state as a value usable in
// any expression, not just an assignment right-hand side. Here it appears in
// two other operand positions -- a conditional-operator condition and an if
// condition -- and its 1/0 result steers the control flow. This mirrors the
// clause's own example, which tests the state directly inside an if.
TEST(ConstraintModeRuntime, NonvoidFormAsExpressionOperand) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int r_before;\n"
      "  int r_after;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    r_before = p.c.constraint_mode() ? 1 : 0;\n"
      "    p.c.constraint_mode(0);\n"
      "    if (p.c.constraint_mode()) r_after = 10; else r_after = 20;\n"
      "  end\n"
      "endmodule\n";
  // Active initially -> the query yields 1, so the conditional operator selects
  // its true arm; after disabling, it yields 0 and the if takes the else arm.
  EXPECT_EQ(RunAndGet(src, "r_before"), 1u);
  EXPECT_EQ(RunAndGet(src, "r_after"), 20u);
}

// 18.9: called as a void function with no constraint identifier, the operation
// applies to ALL constraints within the object -- including those inherited
// from a base class. Two conflicting pins (one inherited, one derived) make
// randomize() unsatisfiable; the no-name form disables every block across the
// hierarchy, so the solve succeeds and querying each block reports inactive.
// This exercises the base-class walk in the no-name branch, distinct from the
// same-class-only case.
TEST(ConstraintModeRuntime, UnnamedFormDisablesInheritedBlocks) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bc { x == 7; }\n"
      "endclass\n"
      "class Der extends Base;\n"
      "  constraint dc { x == 9; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_both;\n"
      "  int ok_all_off;\n"
      "  int q_base;\n"
      "  int q_der;\n"
      "  initial begin\n"
      "    Der d;\n"
      "    d = new;\n"
      "    ok_both = d.randomize();\n"
      "    d.constraint_mode(0);\n"
      "    ok_all_off = d.randomize();\n"
      "    q_base = d.bc.constraint_mode();\n"
      "    q_der = d.dc.constraint_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_both"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_all_off"), 1u);
  EXPECT_EQ(RunAndGet(src, "q_base"), 0u);
  EXPECT_EQ(RunAndGet(src, "q_der"), 0u);
}

// 18.9: the object is any expression that yields the handle in which the
// constraint is defined -- including a subroutine's formal argument, the form
// the clause's own example uses (a function takes the object and calls
// constraint_mode on it). Disabling one of two conflicting pins through the
// formal handle inside a function turns an unsatisfiable solve into one the
// surviving pin binds, proving the call applied through the passed handle.
TEST(ConstraintModeRuntime, ConstraintModeThroughSubroutineArgument) {
  const char* src =
      "class Packet;\n"
      "  rand bit [7:0] v;\n"
      "  constraint c_a { v == 3; }\n"
      "  constraint c_b { v == 8; }\n"
      "endclass\n"
      "function void disable_b(Packet p);\n"
      "  p.c_b.constraint_mode(0);\n"
      "endfunction\n"
      "module t;\n"
      "  int ok_both;\n"
      "  int ok_after;\n"
      "  int rv;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    ok_both = p.randomize();\n"
      "    disable_b(p);\n"
      "    ok_after = p.randomize();\n"
      "    rv = p.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_both"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_after"), 1u);
  EXPECT_EQ(RunAndGet(src, "rv"), 3u);
}

}  // namespace
