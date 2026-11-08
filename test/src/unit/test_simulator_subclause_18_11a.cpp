#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
      "    static CA a = new;\n"
      "    a.y = 200;\n"
      "    okv = a.randomize(x);\n"
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 123u);
  EXPECT_EQ(RunAndGet(src, "ry"), 200u);
}

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
      "    static CA o = new;\n"
      "    o.c = 30;\n"
      "    okv = o.randomize(a, b);\n"
      "    ra = o.a;\n"
      "    rb = o.b;\n"
      "    rc = o.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 10u);
  EXPECT_EQ(RunAndGet(src, "rb"), 20u);
  EXPECT_EQ(RunAndGet(src, "rc"), 30u);
}

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
      "    static CA a = new;\n"
      "    a.x = 5;\n"
      "    a.y = 200;\n"
      "    a.x.rand_mode(0);\n"
      "    okv = a.randomize(x);\n"
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 50u);
  EXPECT_EQ(RunAndGet(src, "ry"), 200u);
}

TEST(InlineRandomControlRuntime, NamedNonRandPropertyIsRandomized) {
  const char* src =
      "class CA;\n"
      "  rand bit [7:0] r;\n"
      "  bit [7:0] s;\n"
      "  constraint c { s == 55; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rs;\n"
      "  int rr;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    a.r = 9;\n"
      "    okv = a.randomize(s);\n"
      "    rs = a.s;\n"
      "    rr = a.r;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rs"), 55u);
  EXPECT_EQ(RunAndGet(src, "rr"), 9u);
}

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
      "    static CA a = new;\n"
      "    a.randomize(c); v0 = a.c;\n"
      "    a.randomize(c); v1 = a.c;\n"
      "    a.randomize(c); v2 = a.c;\n"
      "    a.randomize(c); v3 = a.c;\n"
      "    all_distinct = (v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "                   (v1 != v2) && (v1 != v3) && (v2 != v3);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "all_distinct"), 1u);
}

TEST(InlineRandomControlRuntime, NamedNonRandNotPromotedToCyclical) {
  const char* src =
      "class CA;\n"
      "  bit p;\n"
      "endclass\n"
      "module t;\n"
      "  int repeated;\n"
      "  bit have_prev;\n"
      "  bit prev;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
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
  EXPECT_EQ(RunAndGet(src, "repeated"), 1u);
}

}  // namespace
