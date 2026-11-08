#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StaticConcurrentAssertionSim, StartsFreshAttemptAtEachLeadingClock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk) 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(StaticConcurrentAssertionSim, ReevaluatesConditionOnEachLeadingClock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic cond;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk) cond) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0; cond = 1;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0; cond = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0; cond = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
