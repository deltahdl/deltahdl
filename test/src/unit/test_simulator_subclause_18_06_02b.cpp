#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A Leaf counting its calls, and a Base holding a rand Leaf whose methods
// record the step they ran at, the x they saw and how often they ran.
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

// 18.6.2: randomize() works in three steps: pre_randomize() on the object and
// each enabled random object member, then the new values, then post_randomize()
// on those same objects: pre runs at step 1 seeing x as it was, post at step 2
// seeing the new x below 100, and the Leaf's methods run once each, as the
// design test/src/e2e/pre_post_randomize.sv runs it.
TEST(PrePostRandomizeRun, PreRunsBeforeTheValuesAndPostAfterOnTheTree) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kHooked) +
          "module t;\n"
          "  int ok;\n"
          "  initial begin\n"
          "    Base b = new;\n"
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

// 18.6.2: a derived class that overrides the methods has to call the base's, or
// the base's steps are skipped: a Skips not calling super runs its own methods
// alone, and through a Base handle as well, the methods behaving as virtual
// under the virtual randomize(); a Chains calling super runs both.
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
                     "    Chains ch = new;\n"
                     "    Skips sk = new;\n"
                     "    Base handle = sk;\n"
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

// 18.6.2: post_randomize() runs after the new values are assigned, and
// nothing of randomize() runs after it, so a value it writes to a random
// variable is the value the caller reads -- the method is a hook that can
// change the result, not a notification of it. The constraint keeps the
// solver's own value above 100, so a 5 read back is post_randomize()'s and
// not a draw.
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

// §18.6.2: pre_randomize() is invoked before the new random values are
// computed, so the state variable it writes is what the constraints read in
// that call: each call moves lo to the next hundred, and x follows it.
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

}  // namespace
