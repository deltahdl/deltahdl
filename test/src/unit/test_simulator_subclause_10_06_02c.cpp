#include <gtest/gtest.h>

#include "fixture_simulator.h"

// §10.6.2: the force statement's right-hand side is an expression assigned to
// the target, and §10.7 sizes an assigned value to its target. A singular
// target holds the value at its own width, as it does after a blocking
// assignment; it held the value as evaluated, so `force w = 0;` on a scalar
// net left w holding the literal's 32 bits, width and all, and a wider
// literal forced onto a vector variable widened the variable to it.

using namespace delta;

namespace {

// A scalar net forced with an unsized literal stays one bit wide.
TEST(ForceReleaseSim, ForceOfAScalarNetKeepsItsWidth) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  logic a;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    force w = 0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.width, 1u);
  EXPECT_EQ(w->value.ToUint64(), 0u);
  EXPECT_TRUE(w->is_forced);
}

// A vector variable forced with a wider literal takes the literal's low bits
// and keeps its declared width, §10.7 truncating a wider right-hand side.
TEST(ForceReleaseSim, ForceOfAVectorVariableTruncatesToItsWidth) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    force q = 8'hA5;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);
  EXPECT_EQ(q->value.ToUint64(), 0x5u);
}

// §10.6.2 in an instantiated module: `wire w` declared in M, which top
// instantiates as `m`, is created under "m.w", and §23.9 resolves the bare
// name `w` inside M through the instance. The net lookup (SimContext::FindNet)
// asked for the bare key alone, so the instance's `assign w = 0` wrote the
// variable directly instead of driving the net, and `release w` found no net
// to re-resolve from its drivers: the forced 1 stood after the release. The
// force overrides the driver, so w reads 1 while forced, and the release
// hands w back to the driver, so it reads 0 after: 10.
TEST(ForceReleaseSim, ChildInstanceReleaseReresolvesFromTheInstancesDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  wire w;\n"
      "  int r, forced, released;\n"
      "  assign w = 1'b0;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "    #1 forced = w;\n"
      "    release w;\n"
      "    #1 released = w;\n"
      "    r = forced * 10 + released;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
}

}  // namespace
