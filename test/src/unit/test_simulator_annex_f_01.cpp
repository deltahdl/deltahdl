#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr const char* kOneTick =
    "module m;\n"
    "  logic clk = 0;\n"
    "  logic a = 0;\n"
    "  int sampled = 0;\n"
    "  int live = 0;\n"
    "  int deferred = 0;\n"
    "  function void bump_deferred(); deferred = deferred + 1; endfunction\n"
    "  assert property (@(posedge clk) a) sampled = sampled + 1;\n"
    "  always @(posedge clk) assert (a) live = live + 1;\n"
    "  always @(posedge clk) assert #0 (a) bump_deferred();\n"
    "  initial begin\n"
    "    #5 a = 1;\n"
    "    clk = 1;\n"
    "  end\n"
    "endmodule\n";

TEST(FormalSemanticsGeneral, AConcurrentAssertionIsJudgedOnTheSampledWord) {
  SimFixture f;
  auto* sampled = RunAndFindVar(kOneTick, f, "sampled");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 0u);
}

TEST(FormalSemanticsGeneral, ASimpleImmediateAssertionIsJudgedOnTheLiveValue) {
  SimFixture f;
  auto* live = RunAndFindVar(kOneTick, f, "live");
  ASSERT_NE(live, nullptr);
  EXPECT_EQ(live->value.ToUint64(), 1u);
}

TEST(FormalSemanticsGeneral,
     ADeferredImmediateAssertionIsJudgedOnTheLiveValue) {
  SimFixture f;
  auto* deferred = RunAndFindVar(kOneTick, f, "deferred");
  ASSERT_NE(deferred, nullptr);
  EXPECT_EQ(deferred->value.ToUint64(), 1u);
}

TEST(FormalSemanticsGeneral, TheThreeAgreeWhenTheValueSettledBeforeTheTick) {
  SimFixture f;
  const std::string kSettled =
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  int sampled = 0;\n"
      "  int live = 0;\n"
      "  int deferred = 0;\n"
      "  function void bump_deferred(); deferred = deferred + 1; endfunction\n"
      "  assert property (@(posedge clk) a) sampled = sampled + 1;\n"
      "  always @(posedge clk) assert (a) live = live + 1;\n"
      "  always @(posedge clk) assert #0 (a) bump_deferred();\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n";
  auto* sampled = RunAndFindVar(kSettled, f, "sampled");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 1u);
  auto* live = f.ctx.FindVariable("live");
  ASSERT_NE(live, nullptr);
  EXPECT_EQ(live->value.ToUint64(), 1u);
  auto* deferred = f.ctx.FindVariable("deferred");
  ASSERT_NE(deferred, nullptr);
  EXPECT_EQ(deferred->value.ToUint64(), 1u);
}

}  // namespace
