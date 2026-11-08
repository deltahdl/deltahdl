#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SoftConstraintPriority, LaterSoftInSameBlockOutranksEarlier) {
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
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

TEST(SoftConstraintPriority, LaterConstraintBlockOutranksEarlierBlock) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint lo { soft x == 10; }\n"
      "  constraint hi { soft x == 20; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

TEST(SoftConstraintPriority, InlineSoftOutranksClassSoft) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize() with { soft x == 20; };\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

TEST(SoftConstraintPriority, DerivedClassSoftOutranksSuperclassSoft) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint bpref { soft x == 10; }\n"
      "endclass\n"
      "class D extends B;\n"
      "  constraint dpref { soft x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static D o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

TEST(SoftConstraintPriority, LowerPrioritySoftHonoredWhenHigherConflictsHard) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 30; }\n"
      "  constraint prefs { soft x == 15; soft x == 100; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 15u);
}

TEST(SoftConstraintPriority, BothSoftDiscardedWhenNeitherCanHold) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 5; }\n"
      "  constraint prefs { soft x == 50; soft x == 90; }\n"
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
  EXPECT_GE(RunAndGet(src, "rx"), 0u);
  EXPECT_LE(RunAndGet(src, "rx"), 5u);
  EXPECT_NE(RunAndGet(src, "rx"), 50u);
  EXPECT_NE(RunAndGet(src, "rx"), 90u);
}

TEST(SoftConstraintPriority, RandomizeWithOnlySoftNeverFails) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint prefs { soft x == 1; soft x == 2; soft y == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "    ry = o.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 2u);
  EXPECT_EQ(RunAndGet(src, "ry"), 5u);
}

TEST(SoftConstraintPriority, NonContradictingSoftAllHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint prefs { soft x == 5; soft y == 7; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "    ry = o.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);
  EXPECT_EQ(RunAndGet(src, "ry"), 7u);
}

}  // namespace
