#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InlineConstraintRuntime, InlineWithBlockPinsValue) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == 42; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(InlineConstraintRuntime, InlineWithBlockCombinesWithClassConstraint) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x > 40; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x < 42; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 41u);
}

TEST(InlineConstraintRuntime, InlineWithBlockConflictFailsSolve) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == 20; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
  EXPECT_EQ(RunAndGet(src, "rx"), 0u);
}

TEST(InlineConstraintRuntime, InlineWithBlockSupportsSetMembershipForm) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x inside {30, 31, 32}; x > 30; x < 32; "
      "};\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 31u);
}

TEST(InlineConstraintRuntime, InlineWithBlockReferencesCallerLocal) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int lim;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    lim = 25;\n"
      "    if (p.randomize() with { x == lim; }) rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 25u);
}

TEST(InlineConstraintRuntime, InlineWithBlockReferencesSubroutineArgument) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  function int pin_to(int y);\n"
      "    P p;\n"
      "    int ok;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x == y; };\n"
      "    return p.x;\n"
      "  endfunction\n"
      "  initial rx = pin_to(37);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 37u);
}

TEST(InlineConstraintRuntime, InlineWithNameResolvesToObjectClassFirst) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  constraint c { x > 100; }\n"
      "endclass\n"
      "module t;\n"
      "  bit [7:0] x;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    int ok;\n"
      "    p = new;\n"
      "    x = 5;\n"
      "    ok = p.randomize() with { x < 102; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 101u);
}

TEST(InlineConstraintRuntime, InlineWithBlockSupportsDistForm) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { x dist {42 := 1}; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(InlineConstraintRuntime, InlineWithBlockSupportsImplicationForm) {
  const char* src =
      "class P;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { (a == 0) -> b == 1; };\n"
      "    rb = p.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

TEST(InlineConstraintRuntime, InlineWithBlockSupportsIfElseForm) {
  const char* src =
      "class P;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  constraint fa { a <= 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int rb;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    ok = p.randomize() with { if (a == 0) b == 1; };\n"
      "    rb = p.b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rb"), 1u);
}

TEST(InlineConstraintRuntime,
     RestrictedBlockResolvesUnlistedNameInCallerScope) {
  const char* src =
      "class P;\n"
      "  rand bit [7:0] x;\n"
      "  rand bit [7:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  bit [7:0] y;\n"
      "  int ok;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    P p;\n"
      "    p = new;\n"
      "    y = 55;\n"
      "    ok = p.randomize() with (x) { x == y; };\n"
      "    rx = p.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 55u);
}

}  // namespace
