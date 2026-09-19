#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// §16.12.1: an instance of a named property can be used as a property_spec, and
// the assertion then means what the property's body means in that place. Each
// case here asserts an instance of a property whose body is the clocked boolean
// form and drives the design so the boolean holds at some ticks and not at
// others, then reads the pass and fail counts the action block kept. §16.14.1
// runs the pass statement when the property is true and the fail statement
// when it is false, so the two counts together say at which ticks the property
// was evaluated and what it evaluated to.

using namespace delta;

namespace {

// Three posedges of clk, with req and en changed between the edges so every
// region of a tick sees the same values: req is 0 at the first tick, 1 with en
// 0 at the second, and 1 with en 1 at the third. The property holds at the
// first and third and fails at the second, so the counts are 2 and 1. An
// implementation that evaluated the instance at no tick leaves both at 0, and
// one that evaluated it as an always-true or always-false property gives 3 and
// 0 or 0 and 3.
TEST(PropertyInstanceSim, InstanceAsSpecIsEvaluatedAsItsBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk = 1'b0;\n"
      "  logic req = 1'b0;\n"
      "  logic en = 1'b1;\n"
      "  int passes = 0;\n"
      "  int fails = 0;\n"
      "  property req_only_when_enabled;\n"
      "    @(posedge clk) !req || en;\n"
      "  endproperty\n"
      "  assert property (req_only_when_enabled)\n"
      "    passes = passes + 1;\n"
      "  else\n"
      "    fails = fails + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"  // tick 1: req 0, en 1 -> holds
      "    #5 clk = 0;\n"
      "    req = 1'b1;\n"
      "    en = 1'b0;\n"
      "    #5 clk = 1;\n"  // tick 2: req 1, en 0 -> fails
      "    #5 clk = 0;\n"
      "    en = 1'b1;\n"
      "    #5 clk = 1;\n"  // tick 3: req 1, en 1 -> holds
      "    #5 clk = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* passes = f.ctx.FindVariable("passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  auto* fails = f.ctx.FindVariable("fails");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 1u);
}

// §16.12.1 makes the substitution on the property's body, and a module's
// property declarations are the same in every instance of the module, so an
// assertion in a module instantiated twice is evaluated in both instances. The
// two instances are driven differently: two ticks with the property holding in
// the first, and two with it failing in the second, so the counts tell the
// instances apart and a substitution made for the first instance only leaves
// the second's counts at 0.
TEST(PropertyInstanceSim, InstanceIsEvaluatedInEveryModuleInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module counter(input logic clk, input logic ok);\n"
      "  int passes = 0;\n"
      "  int fails = 0;\n"
      "  property holds;\n"
      "    @(posedge clk) ok;\n"
      "  endproperty\n"
      "  assert property (holds) passes = passes + 1;\n"
      "  else fails = fails + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  counter u_pass(.clk(clk), .ok(1'b1));\n"
      "  counter u_fail(.clk(clk), .ok(1'b0));\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* pass_passes = f.ctx.FindVariable("u_pass.passes");
  ASSERT_NE(pass_passes, nullptr);
  EXPECT_EQ(pass_passes->value.ToUint64(), 2u);
  auto* pass_fails = f.ctx.FindVariable("u_pass.fails");
  ASSERT_NE(pass_fails, nullptr);
  EXPECT_EQ(pass_fails->value.ToUint64(), 0u);
  auto* fail_passes = f.ctx.FindVariable("u_fail.passes");
  ASSERT_NE(fail_passes, nullptr);
  EXPECT_EQ(fail_passes->value.ToUint64(), 0u);
  auto* fail_fails = f.ctx.FindVariable("u_fail.fails");
  ASSERT_NE(fail_fails, nullptr);
  EXPECT_EQ(fail_fails->value.ToUint64(), 2u);
}

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
