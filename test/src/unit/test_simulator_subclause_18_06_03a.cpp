#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(BehaviorOfRandomizationMethods, StaticRandSharedAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static rand bit [7:0] x;\n"
      "  constraint dom { x > 0; x < 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int va, vb, ok;\n"
      "    static C a = new;\n"
      "    static C b = new;\n"
      "    a.x = 200;\n"
      "    ok = a.randomize();\n"
      "    va = a.x;\n"
      "    vb = b.x;\n"
      "    good = (ok == 1 && va == vb && va > 0 && va < 50) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(BehaviorOfRandomizationMethods, StaticRandcSharedAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static randc bit [1:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int va0, vb0, va1, vb1, ok;\n"
      "    static C a = new;\n"
      "    static C b = new;\n"
      "    ok = a.randomize();\n"
      "    va0 = a.x;\n"
      "    vb0 = b.x;\n"
      "    ok = b.randomize();\n"
      "    va1 = a.x;\n"
      "    vb1 = b.x;\n"
      "    good = (va0 == vb0 && va1 == vb1 && va0 != va1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsPreviousValue) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  constraint bad { x == 10; x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int val;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.x = 42;\n"
      "    ok = c.randomize();\n"
      "    val = c.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "val"), 42u);
}

TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsAllPreviousValues) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] a;\n"
      "  rand bit [7:0] b;\n"
      "  constraint bad { a == 1; a == 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int va;\n"
      "  int vb;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.a = 11;\n"
      "    c.b = 22;\n"
      "    ok = c.randomize();\n"
      "    va = c.a;\n"
      "    vb = c.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "va"), 11u);
  EXPECT_EQ(RunAndGet(src, "vb"), 22u);
}

TEST(BehaviorOfRandomizationMethods,
     FailedRandomizeLeavesSharedStaticUnchanged) {
  const char* src =
      "class C;\n"
      "  static rand bit [7:0] x;\n"
      "  constraint bad { x == 10; x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int va;\n"
      "  int vb;\n"
      "  initial begin\n"
      "    static C a = new;\n"
      "    static C b = new;\n"
      "    a.x = 7;\n"
      "    ok = b.randomize();\n"
      "    va = a.x;\n"
      "    vb = b.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "va"), 7u);
  EXPECT_EQ(RunAndGet(src, "vb"), 7u);
}

TEST(BehaviorOfRandomizationMethods, PostRandomizeNotCalledOnFailure) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int posts;\n"
      "  constraint bad { x == 10; x == 20; }\n"
      "  function void post_randomize(); posts = posts + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int posts_after;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    ok = c.randomize();\n"
      "    posts_after = c.posts;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "posts_after"), 0u);
}

TEST(BehaviorOfRandomizationMethods, PostRandomizeCalledOnSuccess) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  int posts;\n"
      "  constraint ok_c { x < 50; }\n"
      "  function void post_randomize(); posts = posts + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int posts_after;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    ok = c.randomize();\n"
      "    posts_after = c.posts;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "posts_after"), 1u);
}

TEST(BehaviorOfRandomizationMethods,
     ObjectRandomStabilityReproducibleFromSeed) {
  const char* src =
      "class C;\n"
      "  rand bit [15:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int same;\n"
      "  initial begin\n"
      "    int oka, okb;\n"
      "    static C a = new;\n"
      "    static C b = new;\n"
      "    a.srandom(100);\n"
      "    oka = a.randomize();\n"
      "    b.srandom(100);\n"
      "    okb = b.randomize();\n"
      "    same = (oka == 1 && okb == 1 && a.x == b.x) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
