#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_multiclock_counts.h"
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

void ExpectItemAsWithoutTheRedundantClock(const std::string& item,
                                          const std::string& plain) {
  MulticlockCounts named = CountsOfAssertionItem(item);
  MulticlockCounts bare = CountsOfMulticlock(plain);
  EXPECT_NE(bare.passes + bare.fails, 0u) << plain;
  EXPECT_EQ(named.passes, bare.passes) << item;
  EXPECT_EQ(named.fails, bare.fails) << item;
  EXPECT_EQ(named.last_pass, bare.last_pass) << item;
}

TEST(FormalSemanticsOverview, ARedundantClockAtAZeroDelayJoinIsDropped) {
  ExpectAsWithoutTheRedundantClock("sig0 ##0 @(posedge clk0) sig1",
                                   "sig0 ##0 sig1");
  ExpectAsWithoutTheRedundantClock("sig0 ##0 @(posedge clk0) 1 ##1 sig1",
                                   "sig0 ##0 1 ##1 sig1");
}

TEST(FormalSemanticsOverview,
     ARedundantClockAtAJoinInsideADeclarationIsDropped) {
  ExpectAsWithoutTheRedundantClock(
      "s0", "sig0 ##0 sig1",
      "  sequence s0; sig0 ##0 @(posedge clk0) sig1; endsequence\n");
  ExpectAsWithoutTheRedundantClock(
      "s1", "sig0 ##1 sig1",
      "  sequence s1; sig0 ##1 @(posedge clk0) sig1; endsequence\n");
  ExpectAsWithoutTheRedundantClock(
      "q0", "sig0 ##0 sig1",
      "  property q0; sig0 ##0 @(posedge clk0) sig1; endproperty\n");
  ExpectAsWithoutTheRedundantClock(
      "q1", "sig0 ##1 sig1",
      "  property q1; sig0 ##1 @(posedge clk0) sig1; endproperty\n");
}

TEST(FormalSemanticsOverview,
     ARedundantClockMatchingTheDefaultClockingIsDropped) {
  for (const char* delay : {"##0", "##1"}) {
    std::string join = std::string("sig0 ") + delay + " sig1";
    ExpectItemAsWithoutTheRedundantClock(
        "  default clocking @(posedge clk0); endclocking\n" +
            CountedAssertion(std::string("sig0 ") + delay +
                             " @(posedge clk0) sig1"),
        join);
  }
}

TEST(FormalSemanticsOverview,
     ARedundantClockMatchingTheInferredProcedureClockIsDropped) {
  for (const char* delay : {"##0", "##1"}) {
    std::string join = std::string("sig0 ") + delay + " sig1";
    ExpectItemAsWithoutTheRedundantClock(
        "  always @(posedge clk0)\n" +
            CountedAssertion(std::string("sig0 ") + delay +
                             " @(posedge clk0) sig1"),
        join);
  }
}

TEST(FormalSemanticsOverview, DISABLED_ARedundantClockUnderNotIsDropped) {
  ExpectAsWithoutTheRedundantClock("not @(posedge clk0) sig0", "not sig0");
  ExpectAsWithoutTheRedundantClock("not (@(posedge clk0) sig0 ##1 sig1)",
                                   "not (sig0 ##1 sig1)");
}

TEST(FormalSemanticsOverview,
     DISABLED_ARedundantClockUnderNotThroughAPropertyInstanceIsDropped) {
  ExpectAsWithoutTheRedundantClock(
      "not q", "not !sig1",
      "  property q; @(posedge clk0) !sig1; endproperty\n");
  ExpectAsWithoutTheRedundantClock(
      "not qn(posedge clk0)", "not !sig1",
      "  property qn(e); @(e) !sig1; endproperty\n");
}

TEST(FormalSemanticsOverview, ARedundantClockInAnAndOrOrOperandIsDropped) {
  ExpectAsWithoutTheRedundantClock(
      "(@(posedge clk0) sig0 ##1 sig1) and (sig0 or sig1)",
      "(sig0 ##1 sig1) and (sig0 or sig1)");
  ExpectAsWithoutTheRedundantClock(
      "(sig1 ##1 sig0) or (@(posedge clk0) sig0 ##1 sig1)",
      "(sig1 ##1 sig0) or (sig0 ##1 sig1)");
}

TEST(FormalSemanticsOverview, ARedundantClockInAnIfOrElseBranchIsDropped) {
  ExpectAsWithoutTheRedundantClock("if (sig0) (@(posedge clk0) 1 ##1 sig1)",
                                   "if (sig0) (1 ##1 sig1)");
  ExpectAsWithoutTheRedundantClock(
      "if (sig0) (@(posedge clk0) 1 ##1 sig1) else (@(posedge clk0) sig1)",
      "if (sig0) (1 ##1 sig1) else (sig1)");
}

}  // namespace
