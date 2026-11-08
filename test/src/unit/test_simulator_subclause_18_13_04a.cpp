#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(GetRandstateSimulation, ObjectStateReturnsNonEmptyString) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    s = o.get_randstate();\n"
      "    n = (s.len() > 0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 1u);
}

TEST(GetRandstateSimulation, ObjectStateReflectsCurrentRngState) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string s1;\n"
      "  string s2;\n"
      "  string s3;\n"
      "  int eq;\n"
      "  int ne;\n"
      "  initial begin\n"
      "    static C o1 = new(7);\n"
      "    static C o2 = new(7);\n"
      "    s1 = o1.get_randstate();\n"
      "    s2 = o2.get_randstate();\n"
      "    eq = (s1 == s2) ? 1 : 0;\n"
      "    ok = o1.randomize();\n"
      "    s3 = o1.get_randstate();\n"
      "    ne = (s1 != s3) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
  EXPECT_EQ(RunAndGet(src, "ne"), 1u);
}

TEST(GetRandstateSimulation, RetrievingObjectStateDoesNotAdvanceStream) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string junk;\n"
      "  int x1;\n"
      "  int x2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new(5);\n"
      "    static C o2 = new(5);\n"
      "    junk = o1.get_randstate();\n"
      "    junk = o1.get_randstate();\n"
      "    ok = o1.randomize();\n"
      "    x1 = o1.a;\n"
      "    ok = o2.randomize();\n"
      "    x2 = o2.a;\n"
      "    same = (x1 == x2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(GetRandstateSimulation, ProcessStateReflectsCurrentRngState) {
  const char* src =
      "module t;\n"
      "  string s1;\n"
      "  string s2;\n"
      "  string s3;\n"
      "  int eq;\n"
      "  int ne;\n"
      "  int a;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    s1 = p.get_randstate();\n"
      "    s2 = p.get_randstate();\n"
      "    eq = (s1 == s2) ? 1 : 0;\n"
      "    a = $urandom;\n"
      "    s3 = p.get_randstate();\n"
      "    ne = (s1 != s3) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "eq"), 1u);
  EXPECT_EQ(RunAndGet(src, "ne"), 1u);
}

TEST(GetRandstateSimulation, ObjectStateIsIndependentOfOtherObjectDraws) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  string state_before;\n"
      "  string state_after;\n"
      "  int unchanged;\n"
      "  initial begin\n"
      "    static C o1 = new(1);\n"
      "    static C o2 = new(2);\n"
      "    state_before = o2.get_randstate();\n"
      "    ok = o1.randomize();\n"
      "    ok = o1.randomize();\n"
      "    state_after = o2.get_randstate();\n"
      "    unchanged = (state_before == state_after) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "unchanged"), 1u);
}

}  // namespace
