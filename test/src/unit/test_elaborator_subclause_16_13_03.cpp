#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/clock_flow.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClockFlow, LinearOperatorFlowsScopeLeftToRight) {
  const std::vector<ClockFlowOperand> kOperands = {{""}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kLinear, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 2u);
  EXPECT_EQ(kResolved[0], "c");
  EXPECT_EQ(kResolved[1], "c");
}

TEST(ClockFlow, LinearOperatorReplacementPersistsToLaterOperands) {
  const std::vector<ClockFlowOperand> kOperands = {{""}, {"d"}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kLinear, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 3u);
  EXPECT_EQ(kResolved[0], "c");
  EXPECT_EQ(kResolved[1], "d");
  EXPECT_EQ(kResolved[2], "d");
}

TEST(ClockFlow, BranchingOperatorDistributesIncomingScope) {
  const std::vector<ClockFlowOperand> kOperands = {{""}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kBranching, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 2u);
  EXPECT_EQ(kResolved[0], "c");
  EXPECT_EQ(kResolved[1], "c");
}

TEST(ClockFlow, BranchingOperatorDoesNotLeakClockToSibling) {
  const std::vector<ClockFlowOperand> kOperands = {{"d"}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kBranching, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 2u);
  EXPECT_EQ(kResolved[0], "d");
  EXPECT_EQ(kResolved[1], "c");
}

TEST(ClockFlow, ScopeFlowsIntoParentheses) {
  EXPECT_EQ(ClockEnteringParentheses("c"), "c");
}

TEST(ClockFlow, ClockInsideParenthesesDoesNotFlowOut) {
  EXPECT_EQ(ClockAfterParentheses("c", "d"), "c");
}

TEST(ClockFlow, ScopeFlowsIntoInstanceRegardlessOfMethod) {
  EXPECT_EQ(ClockEnteringInstance("c", InstanceMethod::kNone), "c");
  EXPECT_EQ(ClockEnteringInstance("c", InstanceMethod::kTriggered), "c");
  EXPECT_EQ(ClockEnteringInstance("c", InstanceMethod::kMatched), "c");
}

TEST(ClockFlow, ClockInInstanceDeclarationDoesNotFlowOut) {
  EXPECT_EQ(ClockAfterInstance("c", "d"), "c");
}

TEST(ClockFlow, ScopeDoesNotFlowIntoDisableCondition) {
  EXPECT_EQ(ClockEnteringDisableCondition("c"), "");
}

TEST(ClockFlow, JuxtaposedClockingEventsKeepTheSecond) {
  EXPECT_EQ(JuxtaposedClockingEvent("d", "c"), "c");
}

TEST(ClockFlow, OperatorWithNoOperandsResolvesToNoClocks) {
  EXPECT_TRUE(
      ResolveOperandClocks(ClockFlowOperator::kLinear, "c", {}).empty());
  EXPECT_TRUE(
      ResolveOperandClocks(ClockFlowOperator::kBranching, "c", {}).empty());
}

TEST(ClockFlow, LinearOperatorWithNoClockInScopeFlowsNoClock) {
  const std::vector<ClockFlowOperand> kOperands = {{""}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kLinear, "", kOperands);
  ASSERT_EQ(kResolved.size(), 2u);
  EXPECT_EQ(kResolved[0], "");
  EXPECT_EQ(kResolved[1], "");
}

TEST(ClockFlow, LinearOperatorLeadingClockReplacesIncomingScope) {
  const std::vector<ClockFlowOperand> kOperands = {{"d"}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kLinear, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 2u);
  EXPECT_EQ(kResolved[0], "d");
  EXPECT_EQ(kResolved[1], "d");
}

TEST(ClockFlow, LinearOperatorAppliesSuccessiveReplacements) {
  const std::vector<ClockFlowOperand> kOperands = {
      {""}, {"d"}, {""}, {"e"}, {""}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kLinear, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 5u);
  EXPECT_EQ(kResolved[0], "c");
  EXPECT_EQ(kResolved[1], "d");
  EXPECT_EQ(kResolved[2], "d");
  EXPECT_EQ(kResolved[3], "e");
  EXPECT_EQ(kResolved[4], "e");
}

TEST(ClockFlow, BranchingOperatorKeepsDistinctOperandClocksIndependent) {
  const std::vector<ClockFlowOperand> kOperands = {{"d"}, {""}, {"e"}};
  const std::vector<ClockScope> kResolved =
      ResolveOperandClocks(ClockFlowOperator::kBranching, "c", kOperands);
  ASSERT_EQ(kResolved.size(), 3u);
  EXPECT_EQ(kResolved[0], "d");
  EXPECT_EQ(kResolved[1], "c");
  EXPECT_EQ(kResolved[2], "e");
}

TEST(ClockFlow, ClockInsideParenthesesDoesNotEscapeIntoEmptyScope) {
  EXPECT_EQ(ClockAfterParentheses("", "d"), "");
}

TEST(ClockFlow, ClockInInstanceDoesNotEscapeIntoEmptyScope) {
  EXPECT_EQ(ClockAfterInstance("", "d"), "");
}

TEST(ClockFlow, DisableConditionHasNoClockWhenNoneInScope) {
  EXPECT_EQ(ClockEnteringDisableCondition(""), "");
}

TEST(ClockFlow, JuxtaposedIdenticalClockingEventsKeepThatClock) {
  EXPECT_EQ(JuxtaposedClockingEvent("c", "c"), "c");
}

std::string JuxtaposedDeclarationIn(const std::string& place,
                                    const std::string& declaration) {
  std::string line = "  " + declaration + "\n";
  std::string use = "  cover property (s);\n";
  std::string instance =
      "module m;\n  logic c0, c1, a, b;\n  w u(c0, c1, a, b);\nendmodule\n";
  if (place == "module") {
    return "module m;\n  logic c0, c1, a, b;\n" + line + use + "endmodule\n";
  }
  if (place == "interface") {
    return "interface w(input logic c0, c1, a, b);\n" + line + use +
           "endinterface\n" + instance;
  }
  if (place == "checker") {
    return "checker w(c0, c1, a, b);\n" + line + use + "endchecker\n" +
           instance;
  }
  return "package pk;\n  logic c0, c1, a, b;\n" + line +
         "endpackage\nmodule m;\n  cover property (pk::s);\nendmodule\n";
}

void ExpectEachJuxtapositionAcceptedIn(const std::string& place) {
  for (const char* op : {"intersect", "and", "or", "within"}) {
    for (const char* clock : {"@(posedge c0) @(posedge c1)", "@(posedge c1)"}) {
      std::string src =
          JuxtaposedDeclarationIn(place, std::string("sequence s; ") + clock +
                                             " a " + op + " b; endsequence");
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrc(src, f);
      EXPECT_EQ(f.diag.ErrorCount(), 0u);
    }
  }
}

TEST(ClockFlow, AJuxtapositionBeforeABranchingOperatorIsOneClockInAPackage) {
  ExpectEachJuxtapositionAcceptedIn("package");
}

TEST(ClockFlow,
     DISABLED_AJuxtapositionBeforeABranchingOperatorIsOneClockInADesignUnit) {
  for (const char* place : {"module", "interface", "checker"})
    ExpectEachJuxtapositionAcceptedIn(place);
}

}  // namespace
