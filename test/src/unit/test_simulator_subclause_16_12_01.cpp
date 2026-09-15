#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.1: an instance of a named property stands as a property_spec, the
// property's body with the actuals substituted, and each instance is an
// assertion of its own. Two instances of p_low over sig, high at ticks 2 and
// 3 of four, and over other, high at 4, count two and one failures apart,
// and an instance of p_guarded, whose body carries a disable iff, is legal
// as a property_spec and is disabled at the tick rst is high, 2.
TEST(PropertyInstantiationSim, EachInstanceIsAnAssertionOfItsOwn) {
  SimFixture f;
  auto* sig_fail = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int tick = 1;\n"
      "  logic sig, other, rst;\n"
      "  int sig_fail = 0, other_fail = 0, guarded_fail = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always #10 tick = tick + 1;\n"
      "  assign sig = tick inside {2, 3};\n"
      "  assign other = tick inside {4};\n"
      "  assign rst = tick inside {2};\n"
      "  property p_low(x);\n"
      "    @(posedge clk) !x;\n"
      "  endproperty\n"
      "  property p_guarded(x, r);\n"
      "    @(posedge clk) disable iff (r) !x;\n"
      "  endproperty\n"
      "  assert property (p_low(sig)) else sig_fail++;\n"
      "  assert property (p_low(other)) else other_fail++;\n"
      "  assert property (p_guarded(sig, rst)) else guarded_fail++;\n"
      "  initial #40 $finish;\n"
      "endmodule\n",
      f, "sig_fail");
  ASSERT_NE(sig_fail, nullptr);
  EXPECT_EQ(sig_fail->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("other_fail")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("guarded_fail")->value.ToUint64(), 1u);
}

}  // namespace
