#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    req = 1'b1;\n"
      "    en = 1'b0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    en = 1'b1;\n"
      "    #5 clk = 1;\n"
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
