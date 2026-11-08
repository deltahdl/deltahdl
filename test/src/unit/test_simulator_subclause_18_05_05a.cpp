#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstraintImplication, ConsequentEnforcedWhenAntecedentTrue) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

TEST(ConstraintImplication, ConsequentIgnoredWhenAntecedentFalse) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a >= 1; a <= 1; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 0u);
}

TEST(ConstraintImplication, AllConsequentConditionsEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit c;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint fc { c <= 1; }\n"
      "  constraint impl { (a == 0) -> (b == 1 && c == 1); }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc"), 1u);
}

TEST(ConstraintImplication, BracedConsequentSetEnforced) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit c;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint fc { c <= 1; }\n"
      "  constraint impl { (a == 0) -> { b == 1; c == 1; } }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc"), 1u);
}

TEST(ConstraintImplication, ConsequentMayBeInequalityConstraint) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit [2:0] b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 7; }\n"
      "  constraint impl { (a == 0) -> b > 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GT(RunAndGet(src, "rb"), 5u);
}

TEST(ConstraintImplication, BareVariableAntecedent) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] m;\n"
      "  rand bit b;\n"
      "  constraint fm { m >= 2; m <= 2; }\n"
      "  constraint fb { b <= 1; }\n"
      "  constraint impl { m -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

TEST(ConstraintImplication, AntecedentDrivenFalseByUnsatisfiableConsequent) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 1; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int ra;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    ra = o.a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 1u);
}

TEST(ConstraintImplication, GeneralIntegralAntecedent) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  rand bit [1:0] b;\n"
      "  constraint fa { a >= 2; a <= 2; }\n"
      "  constraint fb { b <= 3; }\n"
      "  constraint impl { (a > 1) -> b == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rb = o.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 3u);
}

TEST(ConstraintImplication, RandomizeFailsWhenForcedAntecedentImpossible) {
  const char* src =
      "class C;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "  constraint fb { b <= 0; }\n"
      "  constraint impl { (a == 0) -> b == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

TEST(ConstraintImplication, ConsequentOverAWideDomainIsSatisfied) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] kind;\n"
      "  rand int length;\n"
      "  constraint c {\n"
      "    kind == 0 -> length inside {[1:63]};\n"
      "    kind == 1 -> length == 9000;\n"
      "    kind == 2 -> length > 100000;\n"
      "    kind == 3 -> length < -5;\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    static C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      case (o.kind)\n"
      "        0: if (o.length < 1 || o.length > 63) good = 0;\n"
      "        1: if (o.length != 9000) good = 0;\n"
      "        2: if (o.length <= 100000) good = 0;\n"
      "        3: if (o.length >= -5) good = 0;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
