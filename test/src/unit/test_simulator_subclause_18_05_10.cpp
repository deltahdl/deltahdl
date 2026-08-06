#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.5.10's runtime rule end to end. Each program is parsed,
// elaborated, and run; the outcome is copied into module variables the harness
// reads, so the behavior observed is that of parse/elaborate/run applying the
// rule -- not a hand-built solver state.
//
// The shared machinery is a class with two conflicting equality constraints on
// one variable: while both blocks are active the randomize() solve is
// unsatisfiable, and disabling one leaves the survivor pinning the variable so
// the solve succeeds. When the pinning block is qualified 'static',
// constraint_mode() on it through ONE instance must be observed by EVERY other
// instance -- the flip of a second, untouched instance's solve is the visible
// proof.

// 18.5.10: constraint_mode() on a static block affects all instances of the
// class. Disabling the static block through p1 turns it off for p2 as well:
// p2's no-argument query reports it OFF, and p2's randomize() -- which was
// unsatisfiable while the static block conflicted with c_lo -- now succeeds and
// pins x to the surviving constraint's value.
TEST(StaticConstraintMode, StaticModeDisableThroughOneInstanceAffectsAnother) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  static constraint c_pin { x == 20; }\n"
      "  constraint c_lo { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int st_p2;\n"
      "  int ok_p2;\n"
      "  int rx2;\n"
      "  initial begin\n"
      "    P p1;\n"
      "    P p2;\n"
      "    p1 = new;\n"
      "    p2 = new;\n"
      "    p1.c_pin.constraint_mode(0);\n"
      "    st_p2 = p2.c_pin.constraint_mode();\n"
      "    ok_p2 = p2.randomize();\n"
      "    rx2 = p2.x;\n"
      "  end\n"
      "endmodule\n";
  // p2 never touched c_pin, yet it reads OFF because the state is class-wide.
  EXPECT_EQ(RunAndGet(src, "st_p2"), 0u);
  // With the static block disabled, only c_lo binds p2's solve, so it succeeds.
  EXPECT_EQ(RunAndGet(src, "ok_p2"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx2"), 10u);
}

// 18.5.10 (negative / contrast): a non-static block's mode is per-instance, so
// disabling it through q1 does not reach q2. q2 still reports the block ON and
// its solve stays unsatisfiable. This is the closest input the static rule must
// distinguish: identical source but without the 'static' keyword.
TEST(StaticConstraintMode, NonStaticModeDisableStaysPerInstance) {
  const char* src =
      "class Q;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c_pin { x == 20; }\n"
      "  constraint c_lo { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int st_q2;\n"
      "  int ok_q2;\n"
      "  initial begin\n"
      "    Q q1;\n"
      "    Q q2;\n"
      "    q1 = new;\n"
      "    q2 = new;\n"
      "    q1.c_pin.constraint_mode(0);\n"
      "    st_q2 = q2.c_pin.constraint_mode();\n"
      "    ok_q2 = q2.randomize();\n"
      "  end\n"
      "endmodule\n";
  // q2's copy is untouched: still ON, and its solve still conflicts.
  EXPECT_EQ(RunAndGet(src, "st_q2"), 1u);
  EXPECT_EQ(RunAndGet(src, "ok_q2"), 0u);
}

// 18.5.10: re-enabling the static block through one instance restores it for
// every instance. After p1 turns c_pin off then on again, a second instance's
// solve is freed and then re-bound -- unsatisfiable once more.
TEST(StaticConstraintMode, StaticModeReenableThroughOneInstanceAffectsAnother) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  static constraint c_pin { x == 20; }\n"
      "  constraint c_lo { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_off;\n"
      "  int ok_on;\n"
      "  initial begin\n"
      "    P p1;\n"
      "    P p2;\n"
      "    p1 = new;\n"
      "    p2 = new;\n"
      "    p1.c_pin.constraint_mode(0);\n"
      "    ok_off = p2.randomize();\n"
      "    p1.c_pin.constraint_mode(1);\n"
      "    ok_on = p2.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_off"), 1u);
  EXPECT_EQ(RunAndGet(src, "ok_on"), 0u);
}

// 18.5.10: "all instances of that particular class" reaches an inherited static
// block. Here the static block c_pin is declared in a base class (18.5.2
// inheritance) and the conflicting c_lo in the derived class; two derived
// instances are randomized. Disabling c_pin through one derived instance is
// observed by the other -- the shared state lives on the base class that
// declares the block, so the untouched instance reads it OFF and its solve is
// freed. This exercises the walk up the class hierarchy that locates the
// declaring type, which the same-class tests above never reach.
TEST(StaticConstraintMode, InheritedStaticBlockSharedAcrossDerivedInstances) {
  const char* src =
      "class B;\n"
      "  rand bit [7:0] x;\n"
      "  static constraint c_pin { x == 20; }\n"
      "endclass\n"
      "class D extends B;\n"
      "  constraint c_lo { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int st_d2;\n"
      "  int ok_d2;\n"
      "  int rx2;\n"
      "  initial begin\n"
      "    D d1;\n"
      "    D d2;\n"
      "    d1 = new;\n"
      "    d2 = new;\n"
      "    d1.c_pin.constraint_mode(0);\n"
      "    st_d2 = d2.c_pin.constraint_mode();\n"
      "    ok_d2 = d2.randomize();\n"
      "    rx2 = d2.x;\n"
      "  end\n"
      "endmodule\n";
  // The inherited static block reads OFF on d2 though only d1 touched it.
  EXPECT_EQ(RunAndGet(src, "st_d2"), 0u);
  // With the base's static block disabled, only the derived c_lo binds d2.
  EXPECT_EQ(RunAndGet(src, "ok_d2"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx2"), 10u);
}

}  // namespace
