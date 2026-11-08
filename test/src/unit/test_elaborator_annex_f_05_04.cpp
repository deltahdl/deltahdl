#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_local_variable_flow.h"

using namespace delta;

namespace {

using NameSet = std::set<std::string>;

auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

auto Bool() { return SeqBoolean(BoolAtom("a")); }

auto BlockOf(const std::string& name) {
  return SeqIntersect(Samp(name), Samp(name));
}

TEST(LocalVariableFlow, SampleOfBooleanIsEmpty) {
  EXPECT_EQ(SampleLocals(*Bool()), NameSet{});
}

TEST(LocalVariableFlow, SampleOfLocalDeclRemovesDeclaredName) {
  auto inner = SeqConcat(Samp("v"), Samp("w"));
  auto decl = SeqLocalVarDecl("int", "v", inner);
  EXPECT_EQ(SampleLocals(*decl), (NameSet{"w"}));
}

TEST(LocalVariableFlow, SampleOfAssignmentIsTheAssignedName) {
  EXPECT_EQ(SampleLocals(*Samp("v")), (NameSet{"v"}));
}

TEST(LocalVariableFlow, SampleOfParenIsInnerSample) {
  EXPECT_EQ(SampleLocals(*SeqParen(Samp("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, SampleOfBinaryFormsUnionsOperandSamples) {
  EXPECT_EQ(SampleLocals(*SeqConcat(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqFusion(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqOr(Samp("v"), Samp("w"))), (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqIntersect(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
}

TEST(LocalVariableFlow, SampleOfFirstMatchIsInnerSample) {
  EXPECT_EQ(SampleLocals(*SeqFirstMatch(Samp("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, SampleOfRepetitionForms) {
  EXPECT_EQ(SampleLocals(*SeqNullRepeat(Samp("v"))), NameSet{});
  EXPECT_EQ(SampleLocals(*SeqUnboundedRepeat(Samp("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, BlockOfBooleanIsEmpty) {
  EXPECT_EQ(BlockLocals(*Bool()), NameSet{});
}

TEST(LocalVariableFlow, BlockOfLocalDeclRemovesDeclaredName) {
  auto inner = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                            SeqConcat(Samp("v"), Samp("w")));
  auto decl = SeqLocalVarDecl("int", "v", inner);
  EXPECT_EQ(BlockLocals(*decl), (NameSet{"w"}));
}

TEST(LocalVariableFlow, BlockOfAssignmentIsEmpty) {
  EXPECT_EQ(BlockLocals(*Samp("v")), NameSet{});
}

TEST(LocalVariableFlow, BlockOfParenIsInnerBlock) {
  EXPECT_EQ(BlockLocals(*SeqParen(BlockOf("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, BlockOfConcatRemovesNamesThatFlowFromRight) {
  auto left = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                           SeqConcat(Samp("v"), Samp("w")));
  auto seq = SeqConcat(left, Samp("v"));
  EXPECT_EQ(BlockLocals(*seq), (NameSet{"w"}));
}

TEST(LocalVariableFlow, BlockOfFusionRemovesNamesThatFlowFromRight) {
  auto left = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                           SeqConcat(Samp("v"), Samp("w")));
  auto seq = SeqFusion(left, Samp("v"));
  EXPECT_EQ(BlockLocals(*seq), (NameSet{"w"}));
}

TEST(LocalVariableFlow, BlockOfOrUnionsOperandBlocks) {
  EXPECT_EQ(BlockLocals(*SeqOr(BlockOf("v"), BlockOf("w"))),
            (NameSet{"v", "w"}));
}

TEST(LocalVariableFlow, BlockOfIntersectAddsCommonlySampledNames) {
  EXPECT_EQ(BlockLocals(*SeqIntersect(Samp("v"), Samp("v"))), (NameSet{"v"}));
  EXPECT_EQ(BlockLocals(*SeqIntersect(Samp("v"), Samp("w"))), NameSet{});
}

TEST(LocalVariableFlow, BlockOfFirstMatchIsInnerBlock) {
  EXPECT_EQ(BlockLocals(*SeqFirstMatch(BlockOf("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, BlockOfRepetitionForms) {
  EXPECT_EQ(BlockLocals(*SeqNullRepeat(BlockOf("v"))), NameSet{});
  EXPECT_EQ(BlockLocals(*SeqUnboundedRepeat(BlockOf("v"))), (NameSet{"v"}));
}

TEST(LocalVariableFlow, FlowThroughBooleanPassesInputThrough) {
  EXPECT_EQ(FlowLocals({"a"}, *Bool()), (NameSet{"a"}));
}

TEST(LocalVariableFlow, FlowThroughLocalDeclHidesInnerNameButKeepsIncoming) {
  auto decl = SeqLocalVarDecl("int", "v", Samp("v"));
  EXPECT_EQ(FlowLocals({"a"}, *decl), (NameSet{"a"}));
  EXPECT_EQ(FlowLocals({"a", "v"}, *decl), (NameSet{"a", "v"}));
}

TEST(LocalVariableFlow, FlowThroughAssignmentAddsAssignedName) {
  EXPECT_EQ(FlowLocals({"a"}, *Samp("v")), (NameSet{"a", "v"}));
}

TEST(LocalVariableFlow, FlowThroughParenIsInnerFlow) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqParen(Samp("v"))), (NameSet{"a", "v"}));
}

TEST(LocalVariableFlow, FlowThroughConcatAndFusionThreadsBothOperands) {
  auto concat = SeqConcat(Samp("v"), Samp("w"));
  auto fusion = SeqFusion(Samp("v"), Samp("w"));
  EXPECT_EQ(FlowLocals({"a"}, *concat), (NameSet{"a", "v", "w"}));
  EXPECT_EQ(FlowLocals({"a"}, *fusion), (NameSet{"a", "v", "w"}));
}

TEST(LocalVariableFlow, FlowThroughOrIntersectsAlternativeFlows) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqOr(Samp("v"), Samp("w"))), (NameSet{"a"}));
}

TEST(LocalVariableFlow, FlowThroughIntersectSubtractsBlockedNames) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqIntersect(Samp("v"), Samp("v"))),
            (NameSet{"a"}));
}

TEST(LocalVariableFlow, FlowThroughFirstMatchIsInnerFlow) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqFirstMatch(Samp("v"))), (NameSet{"a", "v"}));
}

TEST(LocalVariableFlow, FlowThroughRepetitionForms) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqNullRepeat(Samp("v"))), (NameSet{"a"}));
  EXPECT_EQ(FlowLocals({"a"}, *SeqUnboundedRepeat(Samp("v"))),
            (NameSet{"a", "v"}));
}

TEST(LocalVariableFlow, RemarkFlowEqualsInputUnionEmptyFlowMinusBlock) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  const NameSet kX{"a", "w"};
  NameSet expected = FlowLocals({}, *seq);
  expected.insert(kX.begin(), kX.end());
  for (const std::string& name : BlockLocals(*seq)) {
    expected.erase(name);
  }
  EXPECT_EQ(FlowLocals(kX, *seq), expected);
}

TEST(LocalVariableFlow, RemarkEmptyFlowAndBlockAreDisjoint) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  NameSet intersection;
  const NameSet kEmptyFlow = FlowLocals({}, *seq);
  const NameSet kBlocked = BlockLocals(*seq);
  for (const std::string& name : kEmptyFlow) {
    if (kBlocked.count(name) != 0) {
      intersection.insert(name);
    }
  }
  EXPECT_EQ(intersection, NameSet{});
}

TEST(LocalVariableFlow, RemarkEmptyFlowIsSubsetOfSample) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  const NameSet kEmptyFlow = FlowLocals({}, *seq);
  const NameSet kSampled = SampleLocals(*seq);
  NameSet outside;
  for (const std::string& name : kEmptyFlow) {
    if (kSampled.count(name) == 0) {
      outside.insert(name);
    }
  }
  EXPECT_EQ(outside, NameSet{});
}

TEST(LocalVariableFlow, FlowThroughBooleanWithEmptyInputStaysEmpty) {
  EXPECT_EQ(FlowLocals({}, *Bool()), NameSet{});
}

TEST(LocalVariableFlow, FlowThroughNestedLocalDeclHidesOuterDeclaredName) {
  auto inner = SeqConcat(Samp("w"), Samp("v"));
  auto seq = SeqLocalVarDecl("int", "w", inner);
  EXPECT_EQ(FlowLocals({}, *seq), (NameSet{"v"}));
  EXPECT_EQ(SampleLocals(*seq), (NameSet{"v"}));
}

TEST(LocalVariableFlow, BlockOfConcatRetainsLeftBlockWhenRightFlowsNothing) {
  EXPECT_EQ(BlockLocals(*SeqConcat(BlockOf("v"), Bool())), (NameSet{"v"}));
}

TEST(LocalVariableFlow, FlowThroughIntersectRemovesIncomingBlockedName) {
  EXPECT_EQ(FlowLocals({"v"}, *SeqIntersect(Samp("v"), Samp("v"))), NameSet{});
}

TEST(LocalVariableFlow, BlockOfIntersectCombinesOperandBlocksAndCommonSamples) {
  auto left = SeqConcat(Samp("v"), BlockOf("x"));
  auto right = SeqConcat(Samp("v"), BlockOf("y"));
  EXPECT_EQ(BlockLocals(*SeqIntersect(left, right)), (NameSet{"v", "x", "y"}));
}

}  // namespace
