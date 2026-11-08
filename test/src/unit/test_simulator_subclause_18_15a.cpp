#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ManuallySeedingRandomize,
     HierarchicalObjectSeedingGivesEachObjectOwnSeed) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int diff;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    ok = o2.randomize();\n"
      "    a2 = o2.a;\n"
      "    diff = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "diff"), 1u);
}

TEST(ManuallySeedingRandomize, NewMethodSrandomGovernsMemberRandomization) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static Packet p1 = new(200);\n"
      "    static Packet p2 = new(200);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    same = (h1 == h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(ManuallySeedingRandomize, ConstructorSeedValueControlsResult) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int diff;\n"
      "  initial begin\n"
      "    static Packet p1 = new(200);\n"
      "    static Packet p2 = new(300);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    diff = (h1 != h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "diff"), 1u);
}

TEST(ManuallySeedingRandomize, ExternalSrandomMatchesConstructorSeeding) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static Packet p1 = new(200);\n"
      "    static Packet p2 = new(300);\n"
      "    ok = p1.randomize();\n"
      "    p1.srandom(300);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    same = (h1 == h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(ManuallySeedingRandomize, HierarchicalSeedDerivesFromCreatingThreadRng) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    automatic process pr = process::self();\n"
      "    C o1;\n"
      "    C o2;\n"
      "    pr.srandom(1000);\n"
      "    o1 = new;\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    pr.srandom(1000);\n"
      "    o2 = new;\n"
      "    ok = o2.randomize();\n"
      "    a2 = o2.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(ManuallySeedingRandomize, PerObjectRngIsIndependentAcrossObjects) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    o1.srandom(7);\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    o1.srandom(7);\n"
      "    ok = o2.randomize();\n"
      "    ok = o2.randomize();\n"
      "    ok = o1.randomize();\n"
      "    a2 = o1.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(ManuallySeedingRandomize, ObjectRngIndependentOfOtherRandomizationFuncs) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int junk;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.srandom(77);\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    o.srandom(77);\n"
      "    junk = $urandom;\n"
      "    junk = $urandom;\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
