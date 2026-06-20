#include <gtest/gtest.h>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

using namespace delta;

namespace {

// §F.5.1: the clock rewrite reduces a clocked sequence to "an unclocked
// version". Applying the transformation to @( clk ) a leaves no clock behind.
TEST(ClockRewrite, TransformationProducesUnclockedVersion) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

// §F.5.1: "it is required that the conditions in event controls not be
// dependent upon any local variables." An event condition that names an
// ordinary signal -- not a local of the sequence -- meets the requirement.
TEST(ClockRewrite, EventOnOrdinarySignalIsIndependent) {
  auto seq = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: a clock whose event condition reads a local variable declared in the
// sequence violates the requirement.
TEST(ClockRewrite, EventOnDeclaredLocalIsDependent) {
  // ( int v; @( v ) a ) -- the event control samples the local v.
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: the dependency is forbidden even when the local is reached only
// through the assignment form ( 1, v = e ).
TEST(ClockRewrite, EventOnSampledLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqConcat(SeqLocalVarSampling("v"), clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: a local read buried inside a compound event condition (!v, v & x) is
// still a dependency on a local variable.
TEST(ClockRewrite, EventReadingLocalInsideCompoundConditionIsDependent) {
  auto event = BoolAnd(BoolAtom("clk"), BoolNot(BoolAtom("v")));
  auto clocked = SeqClock(event, SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: declaring a local does not taint an event condition that reads a
// different name.
TEST(ClockRewrite, EventOnDistinctNameIsIndependent) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: a sequence with no event control trivially satisfies the
// requirement.
TEST(ClockRewrite, UnclockedSequenceIsVacuouslyIndependent) {
  auto seq = SeqLocalVarDecl(
      "int", "v",
      SeqConcat(SeqLocalVarSampling("v"), SeqBoolean(BoolAtom("v"))));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: the requirement reaches event controls nested inside another clock.
// Here the outer event is clean but the inner one reads the local v.
TEST(ClockRewrite, NestedClockEventReadingLocalIsDependent) {
  auto inner = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto outer = SeqClock(BoolAtom("clk"), inner);
  auto seq = SeqLocalVarDecl("int", "v", outer);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: the requirement is checked at every event control, including one
// buried in a branch of an or that does not itself sample the local.
TEST(ClockRewrite, ClockInOrBranchReadingLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqOr(clocked, SeqBoolean(BoolAtom("b"))));
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: the requirement constrains event-control conditions, not the Boolean
// guards of the sequence. A constant event control reads nothing, so the local
// v appearing only as a sampled guard leaves the clock independent.
TEST(ClockRewrite, ConstantEventLeavesGuardLocalIndependent) {
  auto clocked = SeqClock(BoolTrue(), SeqBoolean(BoolAtom("v")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqConcat(SeqLocalVarSampling("v"), clocked));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

// §F.5.1: the transformation removes clocks even when several are nested and
// distributed, leaving a fully unclocked sequence.
TEST(ClockRewrite, NestedClocksFullyReduceToUnclocked) {
  auto inner = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("b")));
  auto body = SeqConcat(SeqBoolean(BoolAtom("a")), inner);
  auto clocked = SeqClock(BoolAtom("c1"), body);
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

}  // namespace
