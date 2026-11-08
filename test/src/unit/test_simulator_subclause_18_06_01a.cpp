#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(RandomizeMethod, ReturnsOneAndAssignsValidValue) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint rng { v >= 10; v <= 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    ok = c.randomize();\n"
      "    good = (ok == 1 && c.v >= 10 && c.v <= 20) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizesInstanceSubjectToConstraint) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint c { v == 42; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C p = new;\n"
      "    ok = p.randomize();\n"
      "    good = (ok == 1 && p.v == 42) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, ReturnsZeroWhenUnsatisfiable) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint bad { v == 10; v == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    ok = c.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

TEST(RandomizeMethod, AssignsEveryActiveVariable) {
  const char* src =
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint r {\n"
      "    a >= 0; a <= 5;\n"
      "    b >= 10; b <= 20;\n"
      "    c >= 100; c <= 110;\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 &&\n"
      "            o.a >= 0 && o.a <= 5 &&\n"
      "            o.b >= 10 && o.b <= 20 &&\n"
      "            o.c >= 100 && o.c <= 110) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizesPackedVectorMemberWithinType) {
  const char* src =
      "class C;\n"
      "  rand bit [3:0] nib;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.nib <= 15) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizesSingleBitMember) {
  const char* src =
      "class C;\n"
      "  rand bit flag;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.flag <= 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizesRandcVariable) {
  const char* src =
      "class C;\n"
      "  randc bit [3:0] v;\n"
      "  constraint c { v == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.v == 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizeIsVirtualDispatchedToDynamicType) {
  const char* src =
      "class Base;\n"
      "  rand int b;\n"
      "  constraint cb { b == 5; }\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int d;\n"
      "  constraint cd { d == 9; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    Base bh;\n"
      "    Derived dh;\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.b == 5 && dh.d == 9) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizeInvokedThroughThisInMethod) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  constraint c { v == 7; }\n"
      "  function int run();\n"
      "    return this.randomize();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.run();\n"
      "    good = (ok == 1 && o.v == 7) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(RandomizeMethod, RandomizesReferencedRandObject) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  constraint cx { x == 13; }\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    static Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    rx = ih.x;\n"
      "    good = (ok == 1 && rx == 13) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
