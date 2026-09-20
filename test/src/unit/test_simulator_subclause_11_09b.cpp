#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// tag at all; the value is what says the member reached u as well.
TEST(TaggedUnionEval, AssignedCallResultCarriesTheReturnedTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid -7;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = g();\n"
      "    y = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 10, "11.9"));
}

// §11.9 (printed page 304): reading a member inconsistent with the current
// tag is a run-time error, and the tag `u = g()` gives u is the one g's
// `return tagged Valid -7` gave its result. With the bits copied and no tag,
// `u.Other` raised nothing.
TEST(TaggedUnionEval, AssignedCallResultTagIsCheckedAgainstAnotherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  function u_t g();\n"
      "    return tagged Valid -7;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = g();\n"
      "    y = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            10, "11.9"));
}

// §13.4.1 (printed page 342): a function's value may be given by assigning
// the variable that has the function's own name, and §7.3.2 (printed 151)
// has `k = tagged Valid 3` give it a tag beside the bits, which §13.5.1
// copies into the formal of `f(k())` with the value and §11.9 (printed 304)
// checks the body's read against. The assignment set the tag under the
// function's name alone, so the formal took the result untagged: `a.Valid`
// of `h()`, whose body assigns `tagged Invalid`, raised nothing. The 3 read
// through k's result says the value travels too, whichever way the tag goes.
TEST(TaggedUnionEval, TaggedAssignmentToTheFunctionNameReachesTheFormal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int x, y;\n"
      "  function u_t k();\n"
      "    k = tagged Valid 3;\n"
      "  endfunction\n"
      "  function u_t h();\n"
      "    h = tagged Invalid;\n"
      "  endfunction\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f(k());\n"
      "    y = f(h());\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 11, "11.9"));
}

}  // namespace
