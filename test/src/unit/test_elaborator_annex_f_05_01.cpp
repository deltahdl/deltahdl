#include <gtest/gtest.h>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"

using namespace delta;

namespace {

TEST(ClockRewrite, TransformationProducesUnclockedVersion) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

TEST(ClockRewrite, EventOnOrdinarySignalIsIndependent) {
  auto seq = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnDeclaredLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnSampledLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqConcat(SeqLocalVarSampling("v"), clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventReadingLocalInsideCompoundConditionIsDependent) {
  auto event = BoolAnd(BoolAtom("clk"), BoolNot(BoolAtom("v")));
  auto clocked = SeqClock(event, SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnDistinctNameIsIndependent) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, UnclockedSequenceIsVacuouslyIndependent) {
  auto seq = SeqLocalVarDecl(
      "int", "v",
      SeqConcat(SeqLocalVarSampling("v"), SeqBoolean(BoolAtom("v"))));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, NestedClockEventReadingLocalIsDependent) {
  auto inner = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto outer = SeqClock(BoolAtom("clk"), inner);
  auto seq = SeqLocalVarDecl("int", "v", outer);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, ClockInOrBranchReadingLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqOr(clocked, SeqBoolean(BoolAtom("b"))));
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, ConstantEventLeavesGuardLocalIndependent) {
  auto clocked = SeqClock(BoolTrue(), SeqBoolean(BoolAtom("v")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqConcat(SeqLocalVarSampling("v"), clocked));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, NestedClocksFullyReduceToUnclocked) {
  auto inner = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("b")));
  auto body = SeqConcat(SeqBoolean(BoolAtom("a")), inner);
  auto clocked = SeqClock(BoolAtom("c1"), body);
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

}  // namespace
