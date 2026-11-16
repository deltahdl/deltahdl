#include <gtest/gtest.h>

#include <string>

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

constexpr char kLevels[] =
    "typedef enum bit [3:0] { LO = 1, MID = 4, HI = 9 } lvl_e;\n";

TEST(EnumRandomVariable, ADependedOnEnumStillTakesOnlyNamedConstants) {
  std::string src = std::string(kLevels) +
                    "class Pkt;\n"
                    "  rand lvl_e r;\n"
                    "  rand bit [4:0] w;\n"
                    "  constraint c { w == r + 1; }\n"
                    "endclass\n"
                    "module t;\n"
                    "  int good = 1;\n"
                    "  initial begin\n"
                    "    static Pkt p = new;\n"
                    "    repeat (40) begin\n"
                    "      if (p.randomize() != 1) good = 0;\n"
                    "      if (!(p.r inside {LO, MID, HI})) good = 0;\n"
                    "      if (p.w != p.r + 1) good = 0;\n"
                    "    end\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(EnumRandomVariable, DISABLED_AnUnnamedValueIsNeverChosen) {
  std::string src = std::string(kLevels) +
                    "class Pkt;\n"
                    "  rand lvl_e r;\n"
                    "  int k = 7;\n"
                    "  constraint c { r == k; }\n"
                    "endclass\n"
                    "module t;\n"
                    "  int ok = 5, okn = 5, val;\n"
                    "  initial begin\n"
                    "    static Pkt p = new;\n"
                    "    ok = p.randomize();\n"
                    "    val = p.r;\n"
                    "    p.k = 4;\n"
                    "    okn = p.randomize();\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_NE(RunAndGet(src, "val"), 7u);
  EXPECT_EQ(RunAndGet(src, "okn"), 1u);
}

TEST(EnumRandomVariable, DISABLED_AnUnnamedValueIsNeverChosenInline) {
  std::string src = std::string(kLevels) +
                    "class Pkt;\n"
                    "  rand lvl_e r;\n"
                    "endclass\n"
                    "module t;\n"
                    "  int k = 7;\n"
                    "  int ok_with = 5, ok_std = 5, v_with, v_std;\n"
                    "  lvl_e lr;\n"
                    "  initial begin\n"
                    "    static Pkt p = new;\n"
                    "    ok_with = p.randomize() with { r == k; };\n"
                    "    v_with = p.r;\n"
                    "    ok_std = std::randomize(lr) with { lr == k; };\n"
                    "    v_std = lr;\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_with"), 0u);
  EXPECT_NE(RunAndGet(src, "v_with"), 7u);
  EXPECT_EQ(RunAndGet(src, "ok_std"), 0u);
  EXPECT_NE(RunAndGet(src, "v_std"), 7u);
}

TEST(EnumRandomVariable, AStateEnumHoldingAnUnnamedValueStillSolves) {
  std::string src = std::string(kLevels) +
                    "class Pkt;\n"
                    "  rand bit [3:0] v;\n"
                    "  lvl_e st;\n"
                    "  constraint c { v == st; }\n"
                    "endclass\n"
                    "module t;\n"
                    "  int ok = 5, val;\n"
                    "  initial begin\n"
                    "    static Pkt p = new;\n"
                    "    p.st = lvl_e'(7);\n"
                    "    ok = p.randomize();\n"
                    "    val = p.v;\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "val"), 7u);
}

TEST(EnumRandomVariable, AStateEnumHoldingAnUnnamedValueStillSolvesInline) {
  std::string src = std::string(kLevels) +
                    "class Pkt;\n"
                    "  rand bit [3:0] v;\n"
                    "endclass\n"
                    "module t;\n"
                    "  lvl_e st;\n"
                    "  bit [3:0] lv;\n"
                    "  int ok_with = 5, ok_std = 5, v_with, v_std;\n"
                    "  initial begin\n"
                    "    static Pkt p = new;\n"
                    "    st = lvl_e'(7);\n"
                    "    ok_with = p.randomize() with { v == st; };\n"
                    "    v_with = p.v;\n"
                    "    ok_std = std::randomize(lv) with { lv == st; };\n"
                    "    v_std = lv;\n"
                    "  end\n"
                    "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok_with"), 1u);
  EXPECT_EQ(RunAndGet(src, "v_with"), 7u);
  EXPECT_EQ(RunAndGet(src, "ok_std"), 1u);
  EXPECT_EQ(RunAndGet(src, "v_std"), 7u);
}

TEST(ConstraintOperandTypes, AStringComparisonDecidesAnImplication) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] b;\n"
      "  string s;\n"
      "  constraint c { s == \"abc\" -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int forced = 1, freed = 0;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    obj.s = \"abc\";\n"
      "    repeat (30) begin\n"
      "      if (obj.randomize() != 1 || obj.b != 1) forced = 0;\n"
      "    end\n"
      "    obj.s = \"abd\";\n"
      "    repeat (30) begin\n"
      "      if (obj.randomize() == 1 && obj.b != 1) freed = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "forced"), 1u);
  EXPECT_EQ(RunAndGet(src, "freed"), 1u);
}

TEST(ConstraintOperandTypes, DISABLED_ARealStateVariableBoundsAnIntegralOne) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] lt, le, gt, ge, eq;\n"
      "  real lo = 3.5, hi = 250.5, at = 7.0;\n"
      "  constraint c { lt < lo; le <= lo; gt > hi; ge >= hi; eq == at; }\n"
      "endclass\n"
      "module t;\n"
      "  int good = 1;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (30) begin\n"
      "      if (obj.randomize() != 1) good = 0;\n"
      "      if (obj.lt > 3 || obj.le > 3) good = 0;\n"
      "      if (obj.gt < 251 || obj.ge < 251) good = 0;\n"
      "      if (obj.eq != 7) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(ConstraintOperandTypes,
     DISABLED_ARealStateVariableBoundsAnIntegralOneInline) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] b;\n"
      "endclass\n"
      "module t;\n"
      "  real lim = 3.5;\n"
      "  bit [7:0] v;\n"
      "  int good = 1;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (30) begin\n"
      "      if (obj.randomize() with { b < lim; } != 1) good = 0;\n"
      "      if (obj.b > 3) good = 0;\n"
      "      if (std::randomize(v) with { v < lim; } != 1) good = 0;\n"
      "      if (v > 3) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(ConstraintOperandTypes, DISABLED_ARealLiteralBoundsAnIntegralOne) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] b;\n"
      "  constraint c { b < 2.5; }\n"
      "endclass\n"
      "module t;\n"
      "  int good = 1;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (30) begin\n"
      "      if (obj.randomize() != 1 || obj.b > 2) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(ConstraintOperandTypes, DISABLED_AContradictionThroughARealOperandFails) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] b;\n"
      "  real lim = 1.5;\n"
      "  constraint c { b == 2; b < lim; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 5, okr = 5;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    ok = obj.randomize();\n"
      "    obj.lim = 2.5;\n"
      "    okr = obj.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "okr"), 1u);
}

TEST(ConstraintProperties, InsideDistAndImplicationAreAllMet) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] a, d, m;\n"
      "  rand bit sel;\n"
      "  constraint c { a inside {[10:12], 40};\n"
      "                 d dist { 3 := 1, [20:22] :/ 2 };\n"
      "                 sel -> m == a + 1;\n"
      "                 !sel -> m == d; }\n"
      "endclass\n"
      "module t;\n"
      "  int good = 1;\n"
      "  initial begin\n"
      "    static C obj = new;\n"
      "    repeat (40) begin\n"
      "      if (obj.randomize() != 1) good = 0;\n"
      "      if (!(obj.a inside {[10:12], 40})) good = 0;\n"
      "      if (!(obj.d inside {3, [20:22]})) good = 0;\n"
      "      if (obj.m != (obj.sel ? obj.a + 1 : obj.d)) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
