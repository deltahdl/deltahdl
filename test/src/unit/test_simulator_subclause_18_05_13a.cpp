#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstraintSoft, SoftHonoredWhenCompatibleWithHard) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 40; x <= 60; }\n"
      "  constraint pref { soft x == 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 50u);
}

TEST(ConstraintSoft, SoftAloneIsHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ConstraintSoft, ConflictingSoftDiscardedAndTreatedAsTrue) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 10; x <= 20; }\n"
      "  constraint pref { soft x == 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GE(RunAndGet(src, "rx"), 10u);
  EXPECT_LE(RunAndGet(src, "rx"), 20u);
  EXPECT_NE(RunAndGet(src, "rx"), 50u);
}

TEST(ConstraintSoft, UnsatisfiableHardConstraintsFailSolve) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint bad { x == 10; x == 20; }\n"
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

TEST(ConstraintSoft, ConflictingSoftConstraintsResolvedByDiscarding) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint prefs { soft x == 10; soft x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  uint64_t rx = RunAndGet(src, "rx");
  EXPECT_TRUE(rx == 10u || rx == 20u);
}

TEST(ConstraintSoft, DiscardedSoftDoesNotBiasDistribution) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 1; }\n"
      "  constraint pref { soft x == 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int saw0;\n"
      "  int saw1;\n"
      "  int saw2;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    saw0 = 0;\n"
      "    saw1 = 0;\n"
      "    saw2 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 100; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 0) saw0 = 1;\n"
      "      if (o.x == 1) saw1 = 1;\n"
      "      if (o.x == 2) saw2 = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw0"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw1"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw2"), 0u);
}

TEST(ConstraintSoft, SoftMembershipPreferenceHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 40; x <= 45; }\n"
      "  constraint pref { soft x inside {42, 43}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inset;\n"
      "  int saw42;\n"
      "  int saw43;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inset = 1;\n"
      "    saw42 = 0;\n"
      "    saw43 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 42) saw42 = 1;\n"
      "      else if (o.x == 43) saw43 = 1;\n"
      "      else inset = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "inset"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw42"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw43"), 1u);
}

TEST(ConstraintSoft, SoftImplicationPreferenceHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint fix { y == 1; }\n"
      "  constraint rng { x >= 5; x <= 9; }\n"
      "  constraint pref { soft (y == 1) -> (x == 7); }\n"
      "endclass\n"
      "module t;\n"
      "  int allseven;\n"
      "  int ally1;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    allseven = 1;\n"
      "    ally1 = 1;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 30; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x != 7) allseven = 0;\n"
      "      if (o.y != 1) ally1 = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "allseven"), 1u);
  EXPECT_EQ(RunAndGet(src, "ally1"), 1u);
}

TEST(ConstraintSoft, SoftPreferenceHonoredOverDistConstrainedDomain) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint dst { x dist {5 := 1, 8 := 1}; }\n"
      "  constraint pref { soft x == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);
}

TEST(ConstraintSoft, SoftDistributionHonoredWhenSatisfiable) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x dist {5 := 1, 8 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inset;\n"
      "  int saw5;\n"
      "  int saw8;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inset = 1;\n"
      "    saw5 = 0;\n"
      "    saw8 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 5) saw5 = 1;\n"
      "      else if (o.x == 8) saw8 = 1;\n"
      "      else inset = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "inset"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw5"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw8"), 1u);
}

TEST(ConstraintSoft, SoftDistributionDiscardedWhenConflicting) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint hard { x == 100; }\n"
      "  constraint pref { soft x dist {5 := 1, 8 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 100u);
}

}  // namespace
