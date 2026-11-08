#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SetRandstateSimulation, RestoresCapturedObjectStream) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int b1;\n"
      "  int b2;\n"
      "  int same;\n"
      "  int differ;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    s = o.get_randstate();\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    o.set_randstate(s);\n"
      "    ok = o.randomize();\n"
      "    b1 = o.a;\n"
      "    ok = o.randomize();\n"
      "    b2 = o.a;\n"
      "    same = (a1 == b1 && a2 == b2) ? 1 : 0;\n"
      "    differ = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
  EXPECT_EQ(RunAndGet(src, "differ"), 1u);
}

TEST(SetRandstateSimulation, TransfersStateBetweenObjects) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    // Advance o1, then capture and hand its state to o2.\n"
      "    ok = o1.randomize();\n"
      "    s = o1.get_randstate();\n"
      "    o2.set_randstate(s);\n"
      "    ok = o1.randomize();\n"
      "    ok = o2.randomize();\n"
      "    same = (o1.a == o2.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SetRandstateSimulation, RestoresCapturedProcessStream) {
  const char* src =
      "module t;\n"
      "  string s;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int b1;\n"
      "  int b2;\n"
      "  int same;\n"
      "  int differ;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    s = p.get_randstate();\n"
      "    a1 = $urandom;\n"
      "    a2 = $urandom;\n"
      "    p.set_randstate(s);\n"
      "    b1 = $urandom;\n"
      "    b2 = $urandom;\n"
      "    same = (a1 == b1 && a2 == b2) ? 1 : 0;\n"
      "    differ = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
  EXPECT_EQ(RunAndGet(src, "differ"), 1u);
}

}  // namespace
