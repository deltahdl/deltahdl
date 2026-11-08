#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(RunAndGet(src, "st_p2"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_p2"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx2"), 10u);
}

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
  EXPECT_EQ(RunAndGet(src, "st_q2"), 1u);
  EXPECT_EQ(RunAndGet(src, "ok_q2"), 0u);
}

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
  EXPECT_EQ(RunAndGet(src, "st_d2"), 0u);
  EXPECT_EQ(RunAndGet(src, "ok_d2"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx2"), 10u);
}

}  // namespace
