#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.8's runtime rule end to end. Each program elaborates a
// real class with rand/randc variables, calls rand_mode() from source, and
// copies the outcome to module variables the harness reads -- so the behavior
// observed is that of parse/elaborate/run applying the rule through the
// production rand_mode() dispatch and randomize() path, not a hand-built solver
// state.

// 18.8 / Table 18-3: rand_mode(0) on a named variable makes it inactive; an
// inactive variable is not randomized but held at its current value and treated
// as a state variable by the solver, while the object's remaining active
// variables are still randomized. Here 'held' is pinned to 200 and disabled, so
// randomize() leaves it at 200 and solves 'active' against its constraint.
TEST(RandModeRuntime, DisabledVariableHeldWhileOthersRandomize) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] held;\n"
      "  rand bit [7:0] active;\n"
      "  constraint c { active == 123; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rheld;\n"
      "  int ractive;\n"
      "  initial begin\n"
      "    P p = new;\n"
      "    p.held = 200;\n"
      "    p.held.rand_mode(0);\n"
      "    okv = p.randomize();\n"
      "    rheld = p.held;\n"
      "    ractive = p.active;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rheld"), 200u);
  EXPECT_EQ(RunAndGet(src, "ractive"), 123u);
}

// 18.8: the nonvoid form (called with no argument) returns the current active
// state -- 1 (ON) when active, 0 (OFF) when inactive. All random variables are
// initially active, so the query reads 1 before any change and 0 after
// rand_mode(0).
TEST(RandModeRuntime, NonvoidReturnsActiveState) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int before;\n"
      "  int after;\n"
      "  initial begin\n"
      "    P p = new;\n"
      "    before = p.x.rand_mode();\n"
      "    p.x.rand_mode(0);\n"
      "    after = p.x.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "before"), 1u);
  EXPECT_EQ(RunAndGet(src, "after"), 0u);
}

// 18.8 (Packet example): the void form called with no variable name applies to
// every random variable in the object. Disabling all then re-enabling only
// source_value leaves source_value active (1) and dest_value inactive (0), as
// the nonvoid queries report.
TEST(RandModeRuntime, UnnamedFormDisablesAllThenSelectiveReEnable) {
  const char* src =
      "class Packet;\n"
      "  rand int source_value;\n"
      "  rand int dest_value;\n"
      "endclass\n"
      "module t;\n"
      "  int q_src;\n"
      "  int q_dst;\n"
      "  initial begin\n"
      "    Packet p = new;\n"
      "    p.rand_mode(0);\n"
      "    p.source_value.rand_mode(1);\n"
      "    q_src = p.source_value.rand_mode();\n"
      "    q_dst = p.dest_value.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "q_src"), 1u);
  EXPECT_EQ(RunAndGet(src, "q_dst"), 0u);
}

// 18.8: with every variable disabled by the unnamed void form, randomize()
// draws nothing -- each variable keeps its current value. Both variables are
// pinned to known values and then all turned off, so randomize() succeeds and
// leaves them unchanged (proof that none was drawn a fresh value).
TEST(RandModeRuntime, AllDisabledHoldsEveryValue) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] a;\n"
      "  rand bit [7:0] b;\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int ra;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    P p = new;\n"
      "    p.a = 100;\n"
      "    p.b = 200;\n"
      "    p.rand_mode(0);\n"
      "    okv = p.randomize();\n"
      "    ra = p.a;\n"
      "    rb = p.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 100u);
  EXPECT_EQ(RunAndGet(src, "rb"), 200u);
}

// 18.8 / Table 18-3: rand_mode(1) sets a previously disabled variable active
// again, so randomize() draws it once more. While inactive the variable is a
// state variable held at 9 (and its own constraint x==77 evaluated against that
// held value makes the solve fail); after rand_mode(1) it is randomized and the
// constraint pins it to 77.
TEST(RandModeRuntime, ReEnableRestoresRandomization) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 77; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok_off;\n"
      "  int off_val;\n"
      "  int ok_on;\n"
      "  int on_val;\n"
      "  initial begin\n"
      "    P p = new;\n"
      "    p.x = 9;\n"
      "    p.x.rand_mode(0);\n"
      "    ok_off = p.randomize();\n"
      "    off_val = p.x;\n"
      "    p.x.rand_mode(1);\n"
      "    ok_on = p.randomize();\n"
      "    on_val = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_off"), 0u);
  EXPECT_EQ(RunAndGet(src, "off_val"), 9u);
  EXPECT_EQ(RunAndGet(src, "ok_on"), 1u);
  EXPECT_EQ(RunAndGet(src, "on_val"), 77u);
}

// 18.8: the specified variable may live anywhere in the class hierarchy, so
// rand_mode() reaches a variable inherited from a base class. Declaring the
// disabled variable in a base class (18.4 rand syntax) and driving randomize()
// through a derived handle shows the inherited variable held at its current
// value while the derived class's own active variable is still randomized.
TEST(RandModeRuntime, InheritedRandVariableDisabledAndHeld) {
  const char* src =
      "class Base;\n"
      "  rand bit [7:0] bx;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand bit [7:0] dy;\n"
      "  constraint c { dy == 44; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rbx;\n"
      "  int rdy;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    d.bx = 150;\n"
      "    d.bx.rand_mode(0);\n"
      "    okv = d.randomize();\n"
      "    rbx = d.bx;\n"
      "    rdy = d.dy;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rbx"), 150u);
  EXPECT_EQ(RunAndGet(src, "rdy"), 44u);
}

// 18.8: an inactive variable is treated the same as one never declared rand or
// randc, and this holds for a randc variable too -- once inactive it is not
// cycled through its permutation but held at its current value as a state
// constant, while an active rand sibling is still randomized.
TEST(RandModeRuntime, DisabledRandcVariableHeldAsStateConstant) {
  const char* src =
      "class P;\n"
      "  randc bit [1:0] c;\n"
      "  rand bit [7:0] other;\n"
      "  constraint oc { other == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rc_val;\n"
      "  int ro;\n"
      "  initial begin\n"
      "    P p = new;\n"
      "    p.c = 2;\n"
      "    p.c.rand_mode(0);\n"
      "    okv = p.randomize();\n"
      "    rc_val = p.c;\n"
      "    ro = p.other;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc_val"), 2u);
  EXPECT_EQ(RunAndGet(src, "ro"), 5u);
}

// 18.8: when the random variable is an object handle, rand_mode() changes only
// the mode of that handle variable, not the modes of the random variables
// inside the referenced object. Disabling the rand handle 'h' stops
// randomize() from recursing into the Inner object, so its constrained member
// keeps the pre-set value 3; with the handle left active the same randomize()
// recurses and the constraint pins the member to 55.
TEST(RandModeRuntime, ObjectHandleModeDoesNotCascadeIntoObject) {
  const char* src =
      "class Inner;\n"
      "  rand int v;\n"
      "  constraint cv { v == 55; }\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner h;\n"
      "  function new();\n"
      "    h = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int okd;\n"
      "  int dis_v;\n"
      "  int oke;\n"
      "  int en_v;\n"
      "  Inner id;\n"
      "  Inner ie;\n"
      "  initial begin\n"
      "    Outer pd = new;\n"
      "    id = pd.h;\n"
      "    id.v = 3;\n"
      "    pd.h.rand_mode(0);\n"
      "    okd = pd.randomize();\n"
      "    id = pd.h;\n"
      "    dis_v = id.v;\n"
      "    begin\n"
      "      Outer pe = new;\n"
      "      oke = pe.randomize();\n"
      "      ie = pe.h;\n"
      "      en_v = ie.v;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okd"), 1u);
  EXPECT_EQ(RunAndGet(src, "dis_v"), 3u);
  EXPECT_EQ(RunAndGet(src, "oke"), 1u);
  EXPECT_EQ(RunAndGet(src, "en_v"), 55u);
}

}  // namespace
