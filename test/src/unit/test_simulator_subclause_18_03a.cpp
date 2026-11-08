#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(EnumRandomVariable, SelectsOnlyNamedConstants) {
  const char* src =
      "class Pkt;\n"
      "  typedef enum bit [3:0] { LO = 1, MID = 4, HI = 9 } lvl_e;\n"
      "  rand lvl_e x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_set;\n"
      "  initial begin\n"
      "    static Pkt p = new;\n"
      "    all_in_set = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = p.randomize();\n"
      "      v = p.x;\n"
      "      if (!(v == 1 || v == 4 || v == 9)) all_in_set = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_set"), 1u);
}

TEST(EnumRandomVariable, RandcEnumSelectsOnlyNamedConstants) {
  const char* src =
      "class Pkt;\n"
      "  typedef enum bit [3:0] { LO = 1, MID = 4, HI = 9 } lvl_e;\n"
      "  randc lvl_e x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_set;\n"
      "  initial begin\n"
      "    static Pkt p = new;\n"
      "    all_in_set = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = p.randomize();\n"
      "      v = p.x;\n"
      "      if (!(v == 1 || v == 4 || v == 9)) all_in_set = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_set"), 1u);
}

TEST(ConstraintProperties, ChosenValuesSatisfyConstraints) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] x;\n"
      "  constraint c { x >= 400; x <= 410; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_ok;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    all_ok = 1;\n"
      "    for (int i = 0; i < 20; i++) begin\n"
      "      ok = obj.randomize();\n"
      "      v = obj.x;\n"
      "      if (!(v >= 400 && v <= 410)) all_ok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_ok"), 1u);
}

TEST(ConstraintProperties, OverConstrainedProblemFails) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  constraint contradiction { x == 5; x == 6; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    ok = obj.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

TEST(ConstraintProperties, UnconstrainedVariableStaysInDeclaredRange) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int v;\n"
      "  int all_in_range;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    all_in_range = 1;\n"
      "    for (int i = 0; i < 40; i++) begin\n"
      "      ok = obj.randomize();\n"
      "      v = obj.x;\n"
      "      if (!(v >= 0 && v <= 15)) all_in_range = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "all_in_range"), 1u);
}

}  // namespace
