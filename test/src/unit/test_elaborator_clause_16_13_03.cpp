#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/clock_flow.h"

using namespace delta;

namespace {

// §16.13.3 (core flow rule): the scope of a clocking event flows left to right
// across a linear operator, governing each operand in turn. With clock `c` in
// scope and no operand specifying its own clock, every operand is governed by
// `c`. Mirrors `@(c) x |=> y` where `c` flows across the implication to `y`.
TEST(ClockFlow, LinearOperatorFlowsScopeLeftToRight) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kLinear, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 2u);
  EXPECT_EQ(resolved[0], "c");
  EXPECT_EQ(resolved[1], "c");
}

// §16.13.3 (core flow rule): across a linear operator a clocking event written
// at an operand replaces the flowing scope, and the replacement persists to the
// operands that follow until replaced again. Mirrors `@(c) x ##1 @(d) y ##1 z`:
// `x` is at `c`, then `@(d)` replaces, so `y` and the trailing `z` are at `d`.
TEST(ClockFlow, LinearOperatorReplacementPersistsToLaterOperands) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/"d"},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kLinear, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 3u);
  EXPECT_EQ(resolved[0], "c");
  EXPECT_EQ(resolved[1], "d");
  EXPECT_EQ(resolved[2], "d");
}

// §16.13.3 (core flow rule): a branching operator distributes the incoming
// scope independently to each operand. With `c` in scope and no operand
// specifying its own clock, every operand is governed by `c`. Mirrors `@(c) v
// |=> p and q`, where `c` distributes to both operands of `and`.
TEST(ClockFlow, BranchingOperatorDistributesIncomingScope) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kBranching, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 2u);
  EXPECT_EQ(resolved[0], "c");
  EXPECT_EQ(resolved[1], "c");
}

// §16.13.3 (core flow rule): a clocking event written in one operand of a
// branching operator does not reach a sibling operand; each operand starts from
// the incoming scope. Mirrors `@(c) v |=> (w ##1 @(d) x) and (y ##1 z)`: the
// `@(d)` in the first operand of `and` does not affect the second, which stays
// at `c`.
TEST(ClockFlow, BranchingOperatorDoesNotLeakClockToSibling) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/"d"},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kBranching, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 2u);
  EXPECT_EQ(resolved[0], "d");
  EXPECT_EQ(resolved[1], "c");
}

// §16.13.3 (parentheses rule): the scope of a clocking event flows into a
// parenthesized subexpression. The surrounding clock flows in unchanged.
TEST(ClockFlow, ScopeFlowsIntoParentheses) {
  EXPECT_EQ(ClockEnteringParentheses(/*incoming=*/"c"), "c");
}

// §16.13.3 (parentheses rule): a clocking event introduced inside parentheses
// does not flow out of the enclosing parentheses, so the surrounding scope is
// unchanged. Mirrors `@(c) w ##1 (x ##1 @(d) y) |=> z`: clock `d` does not flow
// out, so `z` is still governed by `c`.
TEST(ClockFlow, ClockInsideParenthesesDoesNotFlowOut) {
  EXPECT_EQ(ClockAfterParentheses(/*incoming=*/"c", /*interior_terminal=*/"d"),
            "c");
}

// §16.13.3 (instance rule): the scope of a clocking event flows into an
// instance of a named property or sequence, regardless of whether the
// `triggered` or `matched` method is applied to the instance.
TEST(ClockFlow, ScopeFlowsIntoInstanceRegardlessOfMethod) {
  EXPECT_EQ(ClockEnteringInstance(/*incoming=*/"c", InstanceMethod::kNone),
            "c");
  EXPECT_EQ(ClockEnteringInstance(/*incoming=*/"c", InstanceMethod::kTriggered),
            "c");
  EXPECT_EQ(ClockEnteringInstance(/*incoming=*/"c", InstanceMethod::kMatched),
            "c");
}

// §16.13.3 (instance rule): a clocking event in the declaration of a property
// or sequence does not flow out of an instance of it, so the surrounding scope
// is unchanged after the instance.
TEST(ClockFlow, ClockInInstanceDeclarationDoesNotFlowOut) {
  EXPECT_EQ(ClockAfterInstance(/*incoming=*/"c", /*declaration_clock=*/"d"),
            "c");
}

// §16.13.3 (disable iff rule): the scope of a clocking event does not flow into
// the disable condition of `disable iff`; the condition carries no clock.
TEST(ClockFlow, ScopeDoesNotFlowIntoDisableCondition) {
  EXPECT_EQ(ClockEnteringDisableCondition(/*incoming=*/"c"), "");
}

// §16.13.3 (juxtaposition rule): juxtaposing two clocking events nullifies the
// first; `@(d) @(c) x` is equivalent to `@(c) x` because the flow of `d` is
// immediately overridden by `c`.
TEST(ClockFlow, JuxtaposedClockingEventsKeepTheSecond) {
  EXPECT_EQ(JuxtaposedClockingEvent(/*first=*/"d", /*second=*/"c"), "c");
}

// §16.13.3 (core flow rule), boundary: an operator with no operands resolves to
// no operand clocks, regardless of kind. Exercises the empty-input path of the
// flow resolution.
TEST(ClockFlow, OperatorWithNoOperandsResolvesToNoClocks) {
  EXPECT_TRUE(
      ResolveOperandClocks(ClockFlowOperator::kLinear, /*incoming=*/"c", {})
          .empty());
  EXPECT_TRUE(
      ResolveOperandClocks(ClockFlowOperator::kBranching, /*incoming=*/"c", {})
          .empty());
}

// §16.13.3 (core flow rule), edge: before any clocking event has been
// specified, no clock is in scope, and a linear operator over clockless
// operands flows no clock — none is fabricated. The empty scope is represented
// by the empty string.
TEST(ClockFlow, LinearOperatorWithNoClockInScopeFlowsNoClock) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kLinear, /*incoming=*/"", operands);
  ASSERT_EQ(resolved.size(), 2u);
  EXPECT_EQ(resolved[0], "");
  EXPECT_EQ(resolved[1], "");
}

// §16.13.3 (core flow rule), edge: a clocking event written at the leading
// operand of a linear operator replaces the incoming scope at that operand and
// the replacement persists onward. Mirrors `@(c) (@(d) x ##1 y)` viewed at the
// inner concatenation: `d` governs `x` and flows to `y`.
TEST(ClockFlow, LinearOperatorLeadingClockReplacesIncomingScope) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/"d"},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kLinear, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 2u);
  EXPECT_EQ(resolved[0], "d");
  EXPECT_EQ(resolved[1], "d");
}

// §16.13.3 (core flow rule), edge: across a linear operator each successive
// clocking event replaces the previous one, and every replacement persists
// until the next. Exercises more than one replacement in a single chain.
TEST(ClockFlow, LinearOperatorAppliesSuccessiveReplacements) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/"d"},
                                                  {/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/"e"},
                                                  {/*explicit_clock=*/""}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kLinear, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 5u);
  EXPECT_EQ(resolved[0], "c");
  EXPECT_EQ(resolved[1], "d");
  EXPECT_EQ(resolved[2], "d");
  EXPECT_EQ(resolved[3], "e");
  EXPECT_EQ(resolved[4], "e");
}

// §16.13.3 (core flow rule), edge: a branching operator distributes the
// incoming scope to each operand independently, so distinct clocking events
// written in different operands stay confined to their own operand and never
// affect a sibling.
TEST(ClockFlow, BranchingOperatorKeepsDistinctOperandClocksIndependent) {
  const std::vector<ClockFlowOperand> operands = {{/*explicit_clock=*/"d"},
                                                  {/*explicit_clock=*/""},
                                                  {/*explicit_clock=*/"e"}};
  const std::vector<ClockScope> resolved = ResolveOperandClocks(
      ClockFlowOperator::kBranching, /*incoming=*/"c", operands);
  ASSERT_EQ(resolved.size(), 3u);
  EXPECT_EQ(resolved[0], "d");
  EXPECT_EQ(resolved[1], "c");
  EXPECT_EQ(resolved[2], "e");
}

// §16.13.3 (parentheses rule), edge: when no clock is in scope around the
// parentheses, a clocking event introduced inside still does not flow out, so
// the surrounding scope remains empty rather than adopting the interior clock.
TEST(ClockFlow, ClockInsideParenthesesDoesNotEscapeIntoEmptyScope) {
  EXPECT_EQ(ClockAfterParentheses(/*incoming=*/"", /*interior_terminal=*/"d"),
            "");
}

// §16.13.3 (instance rule), edge: when no clock is in scope around the
// instance, a clocking event in the declaration does not flow out, so the
// surrounding scope remains empty.
TEST(ClockFlow, ClockInInstanceDoesNotEscapeIntoEmptyScope) {
  EXPECT_EQ(ClockAfterInstance(/*incoming=*/"", /*declaration_clock=*/"d"), "");
}

// §16.13.3 (disable iff rule), edge: the disable condition carries no clocking
// event even when none is in scope to begin with; the barrier is unconditional.
TEST(ClockFlow, DisableConditionHasNoClockWhenNoneInScope) {
  EXPECT_EQ(ClockEnteringDisableCondition(/*incoming=*/""), "");
}

// §16.13.3 (juxtaposition rule), edge: the second clocking event prevails even
// when it names the same clock as the first; the result is that single clock.
TEST(ClockFlow, JuxtaposedIdenticalClockingEventsKeepThatClock) {
  EXPECT_EQ(JuxtaposedClockingEvent(/*first=*/"c", /*second=*/"c"), "c");
}

}  // namespace
