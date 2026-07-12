#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.11's inline random variable control end to end. Each
// program elaborates a real class, calls randomize() with an argument list from
// source, and copies the outcome into module variables the harness reads -- so
// the behavior observed is that of parse/elaborate/run applying the rule
// through the production randomize() path (eval_randomize.cpp), not a
// hand-built solver state. 18.4/18.4.2 supply the rand/randc declarations the
// calls operate on and 18.8 supplies the rand_mode() state that the inline list
// overrides.

// 18.11: when randomize() is called with arguments, those arguments designate
// the complete set of random variables and every other variable in the object
// is considered a state variable. This mechanism is conceptually equivalent to
// rand_mode() calls that enable the named variables and disable the rest. Here
// only 'x' is named, so it is solved to satisfy its constraint while the
// unnamed rand variable 'y' is held at its current value as a state variable.
TEST(InlineRandomControlRuntime, ArgListDesignatesRandomSetUnnamedHeld) {
  const char* src =
      "class CA;\n"
      "  rand bit [7:0] x;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { x == 123; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.y = 200;\n"
      "    okv = a.randomize(x);\n"  // only x is random; y is a state variable
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"),
            123u);  // named -> randomized under constraint
  EXPECT_EQ(RunAndGet(src, "ry"), 200u);  // unnamed -> held, not drawn afresh
}

// 18.11: the argument list may name more than one property, and together those
// arguments form the complete set of random variables for the call; every other
// variable is a state variable. Here 'a' and 'b' are both named and solved to
// satisfy their constraints, while the unnamed 'c' is held at its current
// value.
TEST(InlineRandomControlRuntime, MultipleNamedVariablesRandomizedRestHeld) {
  const char* src =
      "class CA;\n"
      "  rand bit [7:0] a;\n"
      "  rand bit [7:0] b;\n"
      "  rand bit [7:0] c;\n"
      "  constraint ca { a == 10; }\n"
      "  constraint cb { b == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int ra;\n"
      "  int rb;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    CA o = new;\n"
      "    o.c = 30;\n"
      "    okv = o.randomize(a, b);\n"  // a and b random; c is a state variable
      "    ra = o.a;\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 10u);  // named -> randomized under constraint
  EXPECT_EQ(RunAndGet(src, "rb"), 20u);  // named -> randomized under constraint
  EXPECT_EQ(RunAndGet(src, "rc"), 30u);  // unnamed -> held, not drawn afresh
}

// 18.11: naming a variable in the argument list is conceptually equivalent to a
// rand_mode() call that ENABLES it for the duration of this randomize(), so the
// inline list governs the active set even against the object's persistent
// rand_mode() state. Here 'x' is first disabled through 18.8's rand_mode(0);
// naming it in randomize(x) re-activates it for this one call, so it is drawn
// to satisfy its constraint. That the solve succeeds and x reaches 50 (rather
// than staying held at 5, which would fail the x==50 constraint) is only
// possible if the inline list turned the disabled variable back on. The unnamed
// 'y' is held.
TEST(InlineRandomControlRuntime, NamingEnablesVariableDisabledByRandMode) {
  const char* src =
      "class CA;\n"
      "  rand bit [7:0] x;\n"
      "  rand bit [7:0] y;\n"
      "  constraint c { x == 50; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.x = 5;\n"
      "    a.y = 200;\n"
      "    a.x.rand_mode(0);\n"      // 18.8: disable x persistently
      "    okv = a.randomize(x);\n"  // naming x re-enables it for this call
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 50u);  // named -> active despite rand_mode(0)
  EXPECT_EQ(RunAndGet(src, "ry"), 200u);  // unnamed -> state variable, held
}

// 18.11: calling randomize() with arguments allows changing the random mode of
// any class property, even one not declared rand or randc. Here 's' carries no
// random qualifier yet is named, so it becomes an active random variable and is
// solved to satisfy its constraint; the declared rand variable 'r', left
// unnamed, is demoted to a state variable and held at its current value.
TEST(InlineRandomControlRuntime, NamedNonRandPropertyIsRandomized) {
  const char* src =
      "class CA;\n"
      "  rand bit [7:0] r;\n"
      "  bit [7:0] s;\n"  // not declared rand/randc
      "  constraint c { s == 55; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rs;\n"
      "  int rr;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.r = 9;\n"
      "    okv = a.randomize(s);\n"  // promote the non-rand property s
      "    rs = a.s;\n"
      "    rr = a.r;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rs"), 55u);  // non-rand property made random
  EXPECT_EQ(RunAndGet(src, "rr"), 9u);   // declared rand, unnamed -> held
}

// 18.11: the mechanism does not affect the cyclical random mode -- it cannot
// change a cyclical random variable into a noncyclical one. A randc variable
// named in the inline list keeps its randc behavior, cycling through its whole
// declared range with no repeats before any value is drawn twice. Over a 2-bit
// randc, four successive randomize(c) calls therefore return all four distinct
// values.
TEST(InlineRandomControlRuntime, NamedRandcRetainsCyclicalMode) {
  const char* src =
      "class CA;\n"
      "  randc bit [1:0] c;\n"
      "endclass\n"
      "module t;\n"
      "  int v0;\n"
      "  int v1;\n"
      "  int v2;\n"
      "  int v3;\n"
      "  int all_distinct;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    a.randomize(c); v0 = a.c;\n"
      "    a.randomize(c); v1 = a.c;\n"
      "    a.randomize(c); v2 = a.c;\n"
      "    a.randomize(c); v3 = a.c;\n"
      "    all_distinct = (v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "                   (v1 != v2) && (v1 != v3) && (v2 != v3);\n"
      "  end\n"
      "endmodule\n";
  // A still-cyclical randc draws each of 0..3 exactly once across the four
  // calls; had naming stripped the cyclical mode, some value could repeat.
  EXPECT_EQ(RunAndGet(src, "all_distinct"), 1u);
}

// 18.11: the mechanism also cannot change a nonrandom variable into a cyclical
// (randc) one. A property with no random qualifier that is named in the inline
// list is randomized as a noncyclical variable. Over a single-bit domain a
// noncyclical draw repeats consecutively at least once across many calls,
// whereas a randc over {0,1} would strictly alternate and never do so.
TEST(InlineRandomControlRuntime, NamedNonRandNotPromotedToCyclical) {
  const char* src =
      "class CA;\n"
      "  bit p;\n"  // not rand: cannot become randc through naming
      "endclass\n"
      "module t;\n"
      "  int repeated;\n"
      "  bit have_prev;\n"
      "  bit prev;\n"
      "  initial begin\n"
      "    CA a = new;\n"
      "    repeated = 0;\n"
      "    have_prev = 0;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      a.randomize(p);\n"
      "      if (have_prev && a.p == prev) repeated = 1;\n"
      "      prev = a.p;\n"
      "      have_prev = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // A repeat confirms the variable is noncyclical; a randc would never repeat
  // two draws in a row over a two-value domain.
  EXPECT_EQ(RunAndGet(src, "repeated"), 1u);
}

}  // namespace
