#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(RunAndGet(src, "r_before"), 1u);
  EXPECT_EQ(RunAndGet(src, "r_after"), 20u);
}

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

TEST(ConstraintModeRuntime, ABoundOfAnInactiveBlockDoesNotConfineTheDraw) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c_hi { x >= 200; }\n"
      "endclass\n"
      "module t;\n"
      "  int below_off;\n"
      "  int below_on;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    p.c_hi.constraint_mode(0);\n"
      "    repeat (64) begin\n"
      "      void'(p.randomize());\n"
      "      if (p.x < 200) below_off++;\n"
      "    end\n"
      "    p.c_hi.constraint_mode(1);\n"
      "    repeat (64) begin\n"
      "      void'(p.randomize());\n"
      "      if (p.x < 200) below_on++;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "below_off"), 0u);
  EXPECT_EQ(RunAndGet(src, "below_on"), 0u);
}

}  // namespace
