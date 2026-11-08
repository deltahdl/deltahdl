#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string ClockFlowSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  int tick = 1;\n"
         "  logic x, y, z, w, x2, y2, z2, v, w3, x3, y3, z3, xi, yd, zi, xj;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int fail_sum = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #7 clk1 = 1; #6 clk1 = 0;\n"
         "  end\n"
         "  assign x = tick inside {1, 4};\n"
         "  assign y = tick inside {2, 5};\n"
         "  assign z = tick inside {3};\n"
         "  assign w = tick inside {1};\n"
         "  assign x2 = tick inside {2};\n"
         "  assign y2 = tick inside {3};\n"
         "  assign z2 = tick inside {4};\n"
         "  assign v = tick inside {5};\n"
         "  assign w3 = tick inside {6};\n"
         "  assign x3 = tick inside {6};\n"
         "  assign y3 = tick inside {6};\n"
         "  assign z3 = tick inside {7};\n"
         "  assign xi = tick inside {1};\n"
         "  assign yd = tick inside {2};\n"
         "  assign zi = tick inside {2};\n"
         "  assign xj = tick inside {1, 4};\n"
         "  sequence s_d;\n"
         "    @(posedge clk1) yd;\n"
         "  endsequence\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct FlowCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_sum;
};

FlowCounts CountsOfFlow(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ClockFlowSource("  p: assert property (" + spec +
                      ") passes++; else begin fails++; fail_sum += $time; "
                      "end\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* fail_sum = f.ctx.FindVariable("fail_sum");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          fail_sum->value.ToUint64()};
}

TEST(ClockFlow, TheClockFlowsAcrossTheImplication) {
  FlowCounts written = CountsOfFlow(
      "@(posedge clk0) x |=> @(posedge clk0) y ##1 @(posedge clk1) z");
  EXPECT_EQ(written.passes, 7u);
  EXPECT_EQ(written.fails, 1u);
  EXPECT_EQ(written.fail_sum, 57u);
  FlowCounts implied =
      CountsOfFlow("@(posedge clk0) x |=> y ##1 @(posedge clk1) z");
  EXPECT_EQ(implied.passes, 7u);
  EXPECT_EQ(implied.fails, 1u);
  EXPECT_EQ(implied.fail_sum, 57u);
}

TEST(ClockFlow, ConcatenationAndImplicationAreAdjoint) {
  FlowCounts concat =
      CountsOfFlow("@(posedge clk0) x ##1 y |=> @(posedge clk1) z");
  EXPECT_EQ(concat.passes, 7u);
  EXPECT_EQ(concat.fails, 1u);
  EXPECT_EQ(concat.fail_sum, 57u);
  FlowCounts nested =
      CountsOfFlow("@(posedge clk0) x |=> y |=> @(posedge clk1) z");
  EXPECT_EQ(nested.passes, 7u);
  EXPECT_EQ(nested.fails, 1u);
  EXPECT_EQ(nested.fail_sum, 57u);
}

TEST(ClockFlow, AClockInParenthesesFlowsNoFurther) {
  FlowCounts counts =
      CountsOfFlow("@(posedge clk0) w ##1 (x2 ##1 @(posedge clk1) y2) |=> z2");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, TheClockDistributesToTheOperandsOfAnAnd) {
  FlowCounts counts = CountsOfFlow(
      "@(posedge clk0) v |=> (w3 ##1 @(posedge clk1) x3) and (y3 ##1 z3)");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, AClockInAnInstanceFlowsNoFurther) {
  FlowCounts counts = CountsOfFlow("@(posedge clk0) xi |=> s_d ##1 zi");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, TheSecondOfTwoClocksJuxtaposedNullifiesTheFirst) {
  FlowCounts counts = CountsOfFlow("@(posedge clk1) @(posedge clk0) xj");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.fail_sum, 280u);
}

}  // namespace
