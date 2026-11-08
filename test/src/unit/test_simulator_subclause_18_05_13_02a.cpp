#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DisableSoftConstraint, DiscardsAllLowerPrioritySoftsReferencingVariable) {
  const char* disabled =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint p1 { soft x == 3; }\n"
      "  constraint p2 { soft x == 7; }\n"
      "  constraint dis { disable soft x; }\n"
      "endclass\n"
      "module t;\n"
      "  int threes;\n"
      "  int sevens;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    threes = 0;\n"
      "    sevens = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) threes = threes + 1;\n"
      "      if (o.x == 7) sevens = sevens + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto threes = RunAndGet(disabled, "threes");
  EXPECT_GE(threes, 15u);
  EXPECT_LE(threes, 160u);
  auto sevens = RunAndGet(disabled, "sevens");
  EXPECT_GE(sevens, 15u);
  EXPECT_LE(sevens, 160u);

  const char* control =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint p1 { soft x == 3; }\n"
      "  constraint p2 { soft x == 7; }\n"
      "endclass\n"
      "module t;\n"
      "  int sevens;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    sevens = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 7) sevens = sevens + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(control, "sevens"), 600u);
}

TEST(DisableSoftConstraint, DiscardsOnlySoftReferencingTheNamedVariable) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint rng { x >= 0; x <= 9; y >= 0; y <= 9; }\n"
      "  constraint px { soft x == 3; }\n"
      "  constraint py { soft y == 7; }\n"
      "  constraint dis { disable soft x; }\n"
      "endclass\n"
      "module t;\n"
      "  int xhits;\n"
      "  int yhits;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    xhits = 0;\n"
      "    yhits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) xhits = xhits + 1;\n"
      "      if (o.y == 7) yhits = yhits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "yhits"), 600u);
  auto xhits = RunAndGet(src, "xhits");
  EXPECT_GE(xhits, 15u);
  EXPECT_LE(xhits, 160u);
}

TEST(DisableSoftConstraint, SameBlockDirectiveSparesFollowingSoft) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint b1 { soft x == 5; }\n"
      "  constraint b2 { disable soft x; soft x == 8; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 8u);
}

TEST(DisableSoftConstraint, DiscardsNonContradictingSoftWideningSolutionSpace) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint b1 { soft x == 5; }\n"
      "  constraint b2 { disable soft x; soft x dist { 5, 8 }; }\n"
      "endclass\n"
      "module t;\n"
      "  int eights;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    eights = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 8) eights = eights + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto eights = RunAndGet(src, "eights");
  EXPECT_GE(eights, 100u);
  EXPECT_LE(eights, 500u);
}

TEST(DisableSoftConstraint, InlineDirectiveDiscardsClassSoft) {
  const char* disabled =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint pref { soft x == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int hits;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    hits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize() with { disable soft x; });\n"
      "      if (o.x == 3) hits = hits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto hits = RunAndGet(disabled, "hits");
  EXPECT_GE(hits, 15u);
  EXPECT_LE(hits, 160u);

  const char* control =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint pref { soft x == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int hits;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    hits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) hits = hits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(control, "hits"), 600u);
}

}  // namespace
