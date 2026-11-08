#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
      "    static P p = new;\n"
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

TEST(RandModeRuntime, NonvoidReturnsActiveState) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int state_first;\n"
      "  int state_then;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    state_first = p.x.rand_mode();\n"
      "    p.x.rand_mode(0);\n"
      "    state_then = p.x.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "state_first"), 1u);
  EXPECT_EQ(RunAndGet(src, "state_then"), 0u);
}

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
      "    static Packet p = new;\n"
      "    p.rand_mode(0);\n"
      "    p.source_value.rand_mode(1);\n"
      "    q_src = p.source_value.rand_mode();\n"
      "    q_dst = p.dest_value.rand_mode();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "q_src"), 1u);
  EXPECT_EQ(RunAndGet(src, "q_dst"), 0u);
}

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
      "    static P p = new;\n"
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
      "    static P p = new;\n"
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
      "    static Derived d = new;\n"
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
      "    static P p = new;\n"
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
      "    static Outer pd = new;\n"
      "    id = pd.h;\n"
      "    id.v = 3;\n"
      "    pd.h.rand_mode(0);\n"
      "    okd = pd.randomize();\n"
      "    id = pd.h;\n"
      "    dis_v = id.v;\n"
      "    begin\n"
      "      static Outer pe = new;\n"
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

TEST(RandModeRuntime, DisabledVariableIsNotDrawnFromItsSetMembership) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x inside {10, 20, 30}; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    p.x = 3;\n"
      "    p.x.rand_mode(0);\n"
      "    okv = p.randomize();\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 0u);
  EXPECT_EQ(RunAndGet(src, "rx"), 3u);
}

TEST(RandModeRuntime, DisabledVariableIsNotSampledFromItsDistribution) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x dist {10 := 1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    p.x = 3;\n"
      "    p.x.rand_mode(0);\n"
      "    void'(p.randomize());\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 3u);
}

}  // namespace
