#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr const char* kStimulus =
    "  initial begin\n"
    "    #10 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 1;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 0;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "  end\n";

std::string WithAssertion(const std::string& assertion) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n" +
         assertion + kStimulus + "endmodule\n";
}

TEST(FormalSemanticsOverview,
     ADeclarativeAssertionIsEvaluatedOncePerStartingClockEvent) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      WithAssertion("  assert property (@(posedge clk) a) hits = hits + 1;\n"
                    "  else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

TEST(FormalSemanticsOverview, EachMaturedProceduralAttemptIsJudgedOnItsOwn) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      WithAssertion("  always @(posedge clk) assert property (a) hits = hits "
                    "+ 1; else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

}  // namespace
