#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kHooked =
    "class Leaf;\n"
    "  rand bit [7:0] v;\n"
    "  int pre_calls = 0;\n"
    "  int post_calls = 0;\n"
    "  function void pre_randomize();\n"
    "    pre_calls++;\n"
    "  endfunction\n"
    "  function void post_randomize();\n"
    "    post_calls++;\n"
    "  endfunction\n"
    "endclass\n"
    "class Base;\n"
    "  rand bit [7:0] x;\n"
    "  rand Leaf leaf;\n"
    "  int step = 0;\n"
    "  int pre_step = 0;\n"
    "  int post_step = 0;\n"
    "  int pre_x = 0;\n"
    "  int post_x = 0;\n"
    "  int base_pre = 0;\n"
    "  int base_post = 0;\n"
    "  function void pre_randomize();\n"
    "    step++;\n"
    "    pre_step = step;\n"
    "    pre_x = x;\n"
    "    base_pre++;\n"
    "  endfunction\n"
    "  function void post_randomize();\n"
    "    step++;\n"
    "    post_step = step;\n"
    "    post_x = x;\n"
    "    base_post++;\n"
    "  endfunction\n"
    "endclass\n";

TEST(PrePostRandomizeRun, PreRunsBeforeTheValuesAndPostAfterOnTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kHooked) +
          "module t;\n"
          "  int ok;\n"
          "  initial begin\n"
          "    static Base b = new;\n"
          "    b.leaf = new;\n"
          "    b.x = 200;\n"
          "    ok = b.randomize() with { x < 100; };\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", ok, b.pre_step, "
          "b.pre_x, b.post_step,\n"
          "             b.post_x == b.x && b.x < 100, b.leaf.pre_calls, "
          "b.leaf.post_calls);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 200 2 1 1 1\n");
}

TEST(PrePostRandomizeRun, AnOverrideRunsTheBasesStepsThroughSuperAlone) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kHooked) +
                     "class Chains extends Base;\n"
                     "  int own = 0;\n"
                     "  function void pre_randomize();\n"
                     "    super.pre_randomize();\n"
                     "    own++;\n"
                     "  endfunction\n"
                     "  function void post_randomize();\n"
                     "    super.post_randomize();\n"
                     "    own++;\n"
                     "  endfunction\n"
                     "endclass\n"
                     "class Skips extends Base;\n"
                     "  int own = 0;\n"
                     "  function void pre_randomize();\n"
                     "    own++;\n"
                     "  endfunction\n"
                     "  function void post_randomize();\n"
                     "    own++;\n"
                     "  endfunction\n"
                     "endclass\n"
                     "module t;\n"
                     "  initial begin\n"
                     "    static Chains ch = new;\n"
                     "    static Skips sk = new;\n"
                     "    automatic Base handle = sk;\n"
                     "    void'(ch.randomize());\n"
                     "    void'(sk.randomize());\n"
                     "    void'(handle.randomize());\n"
                     "    $display(\"%0d %0d %0d %0d %0d %0d\", ch.base_pre, "
                     "ch.base_post, ch.own,\n"
                     "             sk.base_pre, sk.base_post, sk.own);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 1 2 0 0 4\n");
}

TEST(PrePostRandomizeRun, AValuePostRandomizeAssignsIsWhatTheCallerReads) {
  SimFixture f;
  std::string out = RunCapture(
      "class Fixer;\n"
      "  rand bit [7:0] x;\n"
      "  function void post_randomize();\n"
      "    x = 5;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static Fixer fx = new;\n"
      "    ok = fx.randomize() with { x > 100; };\n"
      "    $display(\"%0d %0d\", ok, fx.x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 5\n");
}

TEST(PrePostRandomizeRun, AStateWrittenByPreRandomizeIsWhatTheCallReads) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int x;\n"
      "  int lo, calls = 0;\n"
      "  constraint c { x inside {[lo:lo + 1]}; }\n"
      "  function void pre_randomize(); calls++; lo = calls * 100; "
      "endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    for (int i = 1; i <= 5; i++) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      if (!(c.x inside {[i * 100:i * 100 + 1]})) bad++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, c.calls);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 5\n");
}

TEST(PrePostRandomizeRun, PostRandomizeReadsTheMembersNewValues) {
  SimFixture f;
  std::string out = RunCapture(
      "class Leaf;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { y > 10; }\n"
      "endclass\n"
      "class Root;\n"
      "  rand bit [7:0] x;\n"
      "  rand Leaf leaf;\n"
      "  int seen = -1;\n"
      "  function void post_randomize(); seen = leaf.y; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static Root r = new;\n"
      "    r.leaf = new;\n"
      "    ok = r.randomize() with (x) { x > 0; };\n"
      "    $display(\"%0d %0d\", ok, r.seen == r.leaf.y && r.leaf.y > 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(PrePostRandomizeRun, AMemberPreRandomizeAllocatesIsSolvedWithTheObject) {
  SimFixture f;
  std::string out = RunCapture(
      "class Item;\n"
      "  rand bit [7:0] y;\n"
      "  int post_y = -1;\n"
      "  function void post_randomize(); post_y = y; endfunction\n"
      "endclass\n"
      "class Holder;\n"
      "  rand bit [7:0] x;\n"
      "  rand Item item;\n"
      "  constraint c { x > 0; item.y == x; }\n"
      "  function void pre_randomize(); item = new; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static Holder h = new;\n"
      "    repeat (4) begin\n"
      "      if (h.randomize() != 1 || h.item.y != h.x ||\n"
      "          h.item.post_y != h.item.y)\n"
      "        bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(PrePostRandomizeRun, AMembersPreSeesItsValuesBeforeTheDraw) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Inner;\n"
                 "  rand bit [7:0] v;\n"
                 "  int seen = -1;\n"
                 "  constraint c { v > 10; }\n"
                 "  function void pre_randomize(); seen = v; endfunction\n"
                 "endclass\n"
                 "class Outer;\n"
                 "  rand Inner in;\n"
                 "  function new(); in = new; endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial begin\n"
                 "    static Outer o = new;\n"
                 "    o.in.v = 7;\n"
                 "    void'(o.randomize());\n"
                 "    $display(\"%0d %0d\", o.in.seen, o.in.v > 10);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "7 1\n");
}

const char* const kCounted =
    "class Inner;\n"
    "  rand bit [7:0] v;\n"
    "  int pre_calls = 0, post_calls = 0;\n"
    "  function void pre_randomize(); pre_calls++; endfunction\n"
    "  function void post_randomize(); post_calls++; endfunction\n"
    "endclass\n";

TEST(PrePostRandomizeRun, AMemberTwoDeepRunsEachHookOncePerCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kCounted) +
                           "class Mid;\n"
                           "  rand Inner i;\n"
                           "  function new(); i = new; endfunction\n"
                           "endclass\n"
                           "class Root;\n"
                           "  rand Mid m;\n"
                           "  function new(); m = new; endfunction\n"
                           "endclass\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    static Root r = new;\n"
                           "    void'(r.randomize());\n"
                           "    void'(r.randomize());\n"
                           "    $display(\"%0d %0d\", r.m.i.pre_calls, "
                           "r.m.i.post_calls);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "2 2\n");
}

TEST(PrePostRandomizeRun, AMemberNotDeclaredRandRunsNoHook) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kCounted) +
                           "class Root;\n"
                           "  rand bit [7:0] x;\n"
                           "  Inner plain;\n"
                           "  function new(); plain = new; endfunction\n"
                           "endclass\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    static Root r = new;\n"
                           "    void'(r.randomize());\n"
                           "    $display(\"%0d %0d\", r.plain.pre_calls, "
                           "r.plain.post_calls);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "0 0\n");
}

TEST(PrePostRandomizeRun, HooksInheritedThroughTwoLevelsRun) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class G;\n"
                       "  rand bit [7:0] v;\n"
                       "  int pre_calls = 0, post_calls = 0;\n"
                       "  function void pre_randomize(); pre_calls++; "
                       "endfunction\n"
                       "  function void post_randomize(); post_calls++; "
                       "endfunction\n"
                       "endclass\n"
                       "class P extends G; endclass\n"
                       "class K extends P; rand bit [7:0] w; endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static K k = new;\n"
                       "    void'(k.randomize());\n"
                       "    $display(\"%0d %0d\", k.pre_calls, k.post_calls);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

const char* const kNonVirtualHooks =
    "class B;\n"
    "  rand bit [7:0] v;\n"
    "  int which = 0;\n"
    "  function void pre_randomize(); which = 1; endfunction\n"
    "  function void post_randomize(); which = 2; endfunction\n"
    "endclass\n"
    "class D extends B;\n"
    "  function void pre_randomize(); which = 11; endfunction\n"
    "  function void post_randomize(); which = 12; endfunction\n"
    "endclass\n";

TEST(PrePostRandomizeRun, AnExplicitPreThroughABaseHandleRunsTheBases) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kNonVirtualHooks) +
                           "module t;\n"
                           "  initial begin\n"
                           "    static D d = new;\n"
                           "    static B bh = d;\n"
                           "    bh.pre_randomize();\n"
                           "    $display(\"%0d\", d.which);\n"
                           "    d.pre_randomize();\n"
                           "    $display(\"%0d\", d.which);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "1\n11\n");
}

TEST(PrePostRandomizeRun, AnExplicitPostThroughABaseHandleRunsTheBases) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::string(kNonVirtualHooks) +
                           "module t;\n"
                           "  initial begin\n"
                           "    static D d = new;\n"
                           "    static B bh = d;\n"
                           "    bh.post_randomize();\n"
                           "    $display(\"%0d\", d.which);\n"
                           "    d.post_randomize();\n"
                           "    $display(\"%0d\", d.which);\n"
                           "  end\n"
                           "endmodule\n",
                       f),
            "2\n12\n");
}

TEST(PrePostRandomizeRun, AForkJoinNoneInAHookRunsItsProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  rand bit [7:0] v;\n"
                       "  int y = 0;\n"
                       "  function void post_randomize(); fork y = 1; "
                       "join_none endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C c = new;\n"
                       "    void'(c.randomize());\n"
                       "    #1 $display(\"%0d\", c.y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

}  // namespace
