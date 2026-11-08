#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InlineConstraintChecker,
     NullChecksConstraintAgainstCurrentValuesReturnsOne) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  rand byte y;\n"
      "  byte v;\n"
      "  byte w;\n"
      "  constraint c1 { x < v && y > w; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    a.x = 1; a.y = 9; a.v = 5; a.w = 3;\n"
      "    okv = a.randomize(null);\n"
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 1u);
  EXPECT_EQ(RunAndGet(src, "ry"), 9u);
}

TEST(InlineConstraintChecker, NullReturnsZeroWhenConstraintViolatedHoldsState) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  rand byte y;\n"
      "  byte v;\n"
      "  byte w;\n"
      "  constraint c1 { x < v && y > w; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    a.x = 5; a.y = 9; a.v = 3; a.w = 3;\n"
      "    okv = a.randomize(null);\n"
      "    rx = a.x;\n"
      "    ry = a.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 0u);
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);
  EXPECT_EQ(RunAndGet(src, "ry"), 9u);
}

TEST(InlineConstraintChecker,
     NullSuppressesRandomizationOfSatisfiableConstraint) {
  const char* src =
      "class CA;\n"
      "  rand byte x;\n"
      "  constraint c { x == 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int chk0;\n"
      "  int rx0;\n"
      "  int chk1;\n"
      "  int rx1;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    static CA b = new;\n"
      "    a.x = 7;\n"
      "    chk0 = a.randomize(null);\n"
      "    rx0 = a.x;\n"
      "    b.x = 7;\n"
      "    chk1 = b.randomize();\n"
      "    rx1 = b.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "chk0"), 0u);
  EXPECT_EQ(RunAndGet(src, "rx0"), 7u);
  EXPECT_EQ(RunAndGet(src, "chk1"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx1"), 100u);
}

TEST(InlineConstraintChecker, NullHoldsRandcVariableAsState) {
  const char* src =
      "class CA;\n"
      "  randc bit [1:0] c;\n"
      "  constraint k { c < 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int okv;\n"
      "  int rc;\n"
      "  initial begin\n"
      "    static CA a = new;\n"
      "    a.c = 2;\n"
      "    okv = a.randomize(null);\n"
      "    rc = a.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "rc"), 2u);
}

TEST(InlineConstraintChecker, NoRandomVariablesActsAsChecker) {
  const char* src =
      "class CB;\n"
      "  byte v;\n"
      "  constraint c { v == 4; }\n"
      "endclass\n"
      "module t;\n"
      "  int oka;\n"
      "  int rva;\n"
      "  int okb;\n"
      "  int rvb;\n"
      "  initial begin\n"
      "    static CB a = new;\n"
      "    static CB b = new;\n"
      "    a.v = 4;\n"
      "    oka = a.randomize();\n"
      "    rva = a.v;\n"
      "    b.v = 9;\n"
      "    okb = b.randomize();\n"
      "    rvb = b.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "oka"), 1u);
  EXPECT_EQ(RunAndGet(src, "rva"), 4u);
  EXPECT_EQ(RunAndGet(src, "okb"), 0u);
  EXPECT_EQ(RunAndGet(src, "rvb"), 9u);
}

TEST(InlineConstraintChecker, NullHoldsRandObjectHandleMemberWithoutRecursing) {
  const char* src =
      "class Sub;\n"
      "  rand byte v;\n"
      "  constraint c { v == 99; }\n"
      "endclass\n"
      "class Top;\n"
      "  rand Sub s;\n"
      "  function new();\n"
      "    s = new;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int chk0;\n"
      "  int rv0;\n"
      "  int chk1;\n"
      "  int rv1;\n"
      "  Sub sa;\n"
      "  Sub sb;\n"
      "  initial begin\n"
      "    static Top a = new;\n"
      "    static Top b = new;\n"
      "    sa = a.s;\n"
      "    sa.v = 7;\n"
      "    chk0 = a.randomize(null);\n"
      "    rv0 = sa.v;\n"
      "    sb = b.s;\n"
      "    sb.v = 7;\n"
      "    chk1 = b.randomize();\n"
      "    rv1 = sb.v;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "chk0"), 1u);
  EXPECT_EQ(RunAndGet(src, "rv0"), 7u);
  EXPECT_EQ(RunAndGet(src, "chk1"), 1u);
  EXPECT_EQ(RunAndGet(src, "rv1"), 99u);
}

}  // namespace
