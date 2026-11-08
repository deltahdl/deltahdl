#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

TEST(PrePostRandomize, DefaultBuiltinsAreNoOpsWhenNotOverridden) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ASSERT_TRUE(solver.Solve());

  ASSERT_EQ(solver.GetValues().size(), 1u);
  const int64_t kX = solver.GetValues().at("x");
  EXPECT_GE(kX, 0);
  EXPECT_LE(kX, 100);
}

TEST(PrePostRandomize, PreThenPostInvokedExactlyOnceInOrder) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  std::vector<std::string> events;
  solver.SetPreRandomize([&]() { events.push_back("pre"); });
  solver.SetPostRandomize([&]() { events.push_back("post"); });

  ASSERT_TRUE(solver.Solve());

  const std::vector<std::string> kExpected = {"pre", "post"};
  EXPECT_EQ(events, kExpected);
}

TEST(PrePostRandomizeFromSource, PreObservesDefaultPostObservesAssignedValue) {
  const char* src =
      "class C;\n"
      "  rand int v;\n"
      "  int pre_saw;\n"
      "  int post_saw;\n"
      "  constraint c { v == 42; }\n"
      "  function void pre_randomize();\n"
      "    pre_saw = v;\n"
      "  endfunction\n"
      "  function void post_randomize();\n"
      "    post_saw = v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    good = (ok == 1 && o.pre_saw == 0 && o.post_saw == 42) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, PostRandomizeAppearsVirtualThroughBaseHandle) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int tag;\n"
      "  constraint cb { v == 1; }\n"
      "  function void post_randomize();\n"
      "    tag = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function void post_randomize();\n"
      "    tag = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Base bh;\n"
      "  Derived dh;\n"
      "  initial begin\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.tag == 2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, InheritedPreRandomizeRunsForDerivedObject) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_pre;\n"
      "  constraint cb { v == 3; }\n"
      "  function void pre_randomize();\n"
      "    base_pre = 7;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int w;\n"
      "  constraint cw { w == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_pre == 7 && d.v == 3 && d.w == 4) ? 1 : "
      "0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, PostRandomizeRunsOnRandObjectMember) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  int inner_post;\n"
      "  constraint cx { x == 9; }\n"
      "  function void post_randomize();\n"
      "    inner_post = x;\n"
      "  endfunction\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    static Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    good = (ok == 1 && ih.inner_post == 9) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, PreRandomizeRunsOnRandObjectMember) {
  const char* src =
      "class Inner;\n"
      "  rand int x;\n"
      "  int inner_pre;\n"
      "  constraint cx { x == 9; }\n"
      "  function void pre_randomize();\n"
      "    inner_pre = 5;\n"
      "  endfunction\n"
      "endclass\n"
      "class Outer;\n"
      "  rand Inner inner;\n"
      "  function new();\n"
      "    inner = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Inner ih;\n"
      "  initial begin\n"
      "    static Outer o = new;\n"
      "    ok = o.randomize();\n"
      "    ih = o.inner;\n"
      "    good = (ok == 1 && ih.inner_pre == 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, OverrideChainsToBaseThroughSuper) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_ran;\n"
      "  constraint c { v == 1; }\n"
      "  function void post_randomize();\n"
      "    base_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int deriv_ran;\n"
      "  function void post_randomize();\n"
      "    super.post_randomize();\n"
      "    deriv_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_ran == 1 && d.deriv_ran == 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, InheritedPostRandomizeRunsForDerivedObject) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_post;\n"
      "  constraint cb { v == 3; }\n"
      "  function void post_randomize();\n"
      "    base_post = v;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  rand int w;\n"
      "  constraint cw { w == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_post == 3 && d.w == 4) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, PreRandomizeAppearsVirtualThroughBaseHandle) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int tag;\n"
      "  constraint cb { v == 1; }\n"
      "  function void pre_randomize();\n"
      "    tag = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function void pre_randomize();\n"
      "    tag = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  Base bh;\n"
      "  Derived dh;\n"
      "  initial begin\n"
      "    dh = new;\n"
      "    bh = dh;\n"
      "    ok = bh.randomize();\n"
      "    good = (ok == 1 && dh.tag == 2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(PrePostRandomizeFromSource, PreOverrideChainsToBaseThroughSuper) {
  const char* src =
      "class Base;\n"
      "  rand int v;\n"
      "  int base_ran;\n"
      "  constraint c { v == 1; }\n"
      "  function void pre_randomize();\n"
      "    base_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int deriv_ran;\n"
      "  function void pre_randomize();\n"
      "    super.pre_randomize();\n"
      "    deriv_ran = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static Derived d = new;\n"
      "    ok = d.randomize();\n"
      "    good = (ok == 1 && d.base_ran == 1 && d.deriv_ran == 1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
