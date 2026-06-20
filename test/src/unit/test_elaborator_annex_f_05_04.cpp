#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_local_variable_flow.h"

using namespace delta;

namespace {

using NameSet = std::set<std::string>;

// A sequence that samples a single local variable: (1, v = e).
auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

// A Boolean leaf b, which neither samples nor blocks any local.
auto Bool() { return SeqBoolean(BoolAtom("a")); }

// (R intersect R) blocks and samples exactly the names sampled by R, because
// §F.5.4 adds sample(R) ∩ sample(R) = sample(R) to the block set.
auto BlockOf(const std::string& name) {
  return SeqIntersect(Samp(name), Samp(name));
}

// §F.5.4: sample(b) = {}.
TEST(LocalVariableFlow, SampleOfBooleanIsEmpty) {
  EXPECT_EQ(SampleLocals(*Bool()), NameSet{});
}

// §F.5.4: sample((t v; R)) = sample(R) - {v}. The declared name is removed
// from what the inner sequence samples.
TEST(LocalVariableFlow, SampleOfLocalDeclRemovesDeclaredName) {
  auto inner = SeqConcat(Samp("v"), Samp("w"));
  auto decl = SeqLocalVarDecl("int", "v", inner);
  EXPECT_EQ(SampleLocals(*decl), (NameSet{"w"}));
}

// §F.5.4: sample((1, v = e)) = {v}.
TEST(LocalVariableFlow, SampleOfAssignmentIsTheAssignedName) {
  EXPECT_EQ(SampleLocals(*Samp("v")), (NameSet{"v"}));
}

// §F.5.4: sample((R)) = sample(R) -- parentheses are transparent.
TEST(LocalVariableFlow, SampleOfParenIsInnerSample) {
  EXPECT_EQ(SampleLocals(*SeqParen(Samp("v"))), (NameSet{"v"}));
}

// §F.5.4: sample is the union of operand samples for ##1, ##0, or, intersect.
TEST(LocalVariableFlow, SampleOfBinaryFormsUnionsOperandSamples) {
  EXPECT_EQ(SampleLocals(*SeqConcat(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqFusion(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqOr(Samp("v"), Samp("w"))), (NameSet{"v", "w"}));
  EXPECT_EQ(SampleLocals(*SeqIntersect(Samp("v"), Samp("w"))),
            (NameSet{"v", "w"}));
}

// §F.5.4: sample(first_match(R)) = sample(R).
TEST(LocalVariableFlow, SampleOfFirstMatchIsInnerSample) {
  EXPECT_EQ(SampleLocals(*SeqFirstMatch(Samp("v"))), (NameSet{"v"}));
}

// §F.5.4: sample(R[*0]) = {} and sample(R[*1:$]) = sample(R).
TEST(LocalVariableFlow, SampleOfRepetitionForms) {
  EXPECT_EQ(SampleLocals(*SeqNullRepeat(Samp("v"))), NameSet{});
  EXPECT_EQ(SampleLocals(*SeqUnboundedRepeat(Samp("v"))), (NameSet{"v"}));
}

// §F.5.4: block(b) = {}.
TEST(LocalVariableFlow, BlockOfBooleanIsEmpty) {
  EXPECT_EQ(BlockLocals(*Bool()), NameSet{});
}

// §F.5.4: block((t v; R)) = block(R) - {v}.
TEST(LocalVariableFlow, BlockOfLocalDeclRemovesDeclaredName) {
  auto inner = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                            SeqConcat(Samp("v"), Samp("w")));
  auto decl = SeqLocalVarDecl("int", "v", inner);
  EXPECT_EQ(BlockLocals(*decl), (NameSet{"w"}));
}

// §F.5.4: block((1, v = e)) = {}.
TEST(LocalVariableFlow, BlockOfAssignmentIsEmpty) {
  EXPECT_EQ(BlockLocals(*Samp("v")), NameSet{});
}

// §F.5.4: block((R)) = block(R).
TEST(LocalVariableFlow, BlockOfParenIsInnerBlock) {
  EXPECT_EQ(BlockLocals(*SeqParen(BlockOf("v"))), (NameSet{"v"}));
}

// §F.5.4: block((R1 ##1 R2)) = (block(R1) - flow({}, R2)) U block(R2). A name
// blocked by R1 is freed when R2 makes it flow out on its own; another stays.
TEST(LocalVariableFlow, BlockOfConcatRemovesNamesThatFlowFromRight) {
  auto left = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                           SeqConcat(Samp("v"), Samp("w")));  // blocks {v, w}
  auto seq = SeqConcat(left, Samp("v"));  // R2 makes v flow out
  EXPECT_EQ(BlockLocals(*seq), (NameSet{"w"}));
}

// §F.5.4: block((R1 ##0 R2)) uses the same rule as ##1.
TEST(LocalVariableFlow, BlockOfFusionRemovesNamesThatFlowFromRight) {
  auto left = SeqIntersect(SeqConcat(Samp("v"), Samp("w")),
                           SeqConcat(Samp("v"), Samp("w")));  // blocks {v, w}
  auto seq = SeqFusion(left, Samp("v"));
  EXPECT_EQ(BlockLocals(*seq), (NameSet{"w"}));
}

// §F.5.4: block((R1 or R2)) = block(R1) U block(R2).
TEST(LocalVariableFlow, BlockOfOrUnionsOperandBlocks) {
  EXPECT_EQ(BlockLocals(*SeqOr(BlockOf("v"), BlockOf("w"))),
            (NameSet{"v", "w"}));
}

// §F.5.4: block((R1 intersect R2)) =
// block(R1) U block(R2) U (sample(R1) ∩ sample(R2)). Names sampled in both
// operands are blocked even when neither operand blocks them alone.
TEST(LocalVariableFlow, BlockOfIntersectAddsCommonlySampledNames) {
  EXPECT_EQ(BlockLocals(*SeqIntersect(Samp("v"), Samp("v"))), (NameSet{"v"}));
  EXPECT_EQ(BlockLocals(*SeqIntersect(Samp("v"), Samp("w"))), NameSet{});
}

// §F.5.4: block(first_match(R)) = block(R).
TEST(LocalVariableFlow, BlockOfFirstMatchIsInnerBlock) {
  EXPECT_EQ(BlockLocals(*SeqFirstMatch(BlockOf("v"))), (NameSet{"v"}));
}

// §F.5.4: block(R[*0]) = {} and block(R[*1:$]) = block(R).
TEST(LocalVariableFlow, BlockOfRepetitionForms) {
  EXPECT_EQ(BlockLocals(*SeqNullRepeat(BlockOf("v"))), NameSet{});
  EXPECT_EQ(BlockLocals(*SeqUnboundedRepeat(BlockOf("v"))), (NameSet{"v"}));
}

// §F.5.4: flow(X, b) = X.
TEST(LocalVariableFlow, FlowThroughBooleanPassesInputThrough) {
  EXPECT_EQ(FlowLocals({"a"}, *Bool()), (NameSet{"a"}));
}

// §F.5.4: flow(X, (t v; R)) = (X ∩ {v}) U (flow(X - {v}, R) - {v}). A v
// produced inside the declaration does not escape, but an incoming v survives.
TEST(LocalVariableFlow, FlowThroughLocalDeclHidesInnerNameButKeepsIncoming) {
  auto decl = SeqLocalVarDecl("int", "v", Samp("v"));
  EXPECT_EQ(FlowLocals({"a"}, *decl), (NameSet{"a"}));
  EXPECT_EQ(FlowLocals({"a", "v"}, *decl), (NameSet{"a", "v"}));
}

// §F.5.4: flow(X, (1, v = e)) = X U {v}.
TEST(LocalVariableFlow, FlowThroughAssignmentAddsAssignedName) {
  EXPECT_EQ(FlowLocals({"a"}, *Samp("v")), (NameSet{"a", "v"}));
}

// §F.5.4: flow(X, (R)) = flow(X, R).
TEST(LocalVariableFlow, FlowThroughParenIsInnerFlow) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqParen(Samp("v"))), (NameSet{"a", "v"}));
}

// §F.5.4: flow(X, (R1 ##1 R2)) and flow(X, (R1 ##0 R2)) thread X through R1
// then R2.
TEST(LocalVariableFlow, FlowThroughConcatAndFusionThreadsBothOperands) {
  auto concat = SeqConcat(Samp("v"), Samp("w"));
  auto fusion = SeqFusion(Samp("v"), Samp("w"));
  EXPECT_EQ(FlowLocals({"a"}, *concat), (NameSet{"a", "v", "w"}));
  EXPECT_EQ(FlowLocals({"a"}, *fusion), (NameSet{"a", "v", "w"}));
}

// §F.5.4: flow(X, (R1 or R2)) = flow(X, R1) ∩ flow(X, R2). Only names that
// escape both alternatives flow out.
TEST(LocalVariableFlow, FlowThroughOrIntersectsAlternativeFlows) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqOr(Samp("v"), Samp("w"))), (NameSet{"a"}));
}

// §F.5.4: flow(X, (R1 intersect R2)) =
// (flow(X, R1) U flow(X, R2)) - block((R1 intersect R2)). The commonly sampled
// name is blocked, so it does not flow out.
TEST(LocalVariableFlow, FlowThroughIntersectSubtractsBlockedNames) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqIntersect(Samp("v"), Samp("v"))),
            (NameSet{"a"}));
}

// §F.5.4: flow(X, first_match(R)) = flow(X, R).
TEST(LocalVariableFlow, FlowThroughFirstMatchIsInnerFlow) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqFirstMatch(Samp("v"))), (NameSet{"a", "v"}));
}

// §F.5.4: flow(X, R[*0]) = X and flow(X, R[*1:$]) = flow(X, R).
TEST(LocalVariableFlow, FlowThroughRepetitionForms) {
  EXPECT_EQ(FlowLocals({"a"}, *SeqNullRepeat(Samp("v"))), (NameSet{"a"}));
  EXPECT_EQ(FlowLocals({"a"}, *SeqUnboundedRepeat(Samp("v"))),
            (NameSet{"a", "v"}));
}

// §F.5.4 remark: flow(X, R) = (X U flow({}, R)) - block(R).
TEST(LocalVariableFlow, RemarkFlowEqualsInputUnionEmptyFlowMinusBlock) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  const NameSet x{"a", "w"};
  NameSet expected = FlowLocals({}, *seq);
  expected.insert(x.begin(), x.end());
  for (const std::string& name : BlockLocals(*seq)) {
    expected.erase(name);
  }
  EXPECT_EQ(FlowLocals(x, *seq), expected);
}

// §F.5.4 remark: flow({}, R) and block(R) are disjoint.
TEST(LocalVariableFlow, RemarkEmptyFlowAndBlockAreDisjoint) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  NameSet intersection;
  const NameSet empty_flow = FlowLocals({}, *seq);
  const NameSet blocked = BlockLocals(*seq);
  for (const std::string& name : empty_flow) {
    if (blocked.count(name) != 0) {
      intersection.insert(name);
    }
  }
  EXPECT_EQ(intersection, NameSet{});
}

// §F.5.4 remark: flow({}, R) is a subset of sample(R).
TEST(LocalVariableFlow, RemarkEmptyFlowIsSubsetOfSample) {
  auto seq = SeqConcat(Samp("v"), SeqIntersect(Samp("w"), Samp("w")));
  const NameSet empty_flow = FlowLocals({}, *seq);
  const NameSet sampled = SampleLocals(*seq);
  NameSet outside;
  for (const std::string& name : empty_flow) {
    if (sampled.count(name) == 0) {
      outside.insert(name);
    }
  }
  EXPECT_EQ(outside, NameSet{});
}

// §F.5.4 edge case for flow(X, b) = X: with an empty input set nothing flows
// out of a Boolean.
TEST(LocalVariableFlow, FlowThroughBooleanWithEmptyInputStaysEmpty) {
  EXPECT_EQ(FlowLocals({}, *Bool()), NameSet{});
}

// §F.5.4 edge case combining sample S2, flow F2, and flow F5: a name declared
// by an outer (t v; R) is stripped at the declaration boundary even though it
// is sampled inside, while a different name sampled alongside it still flows
// out. flow({}, (t w; (w ##1 v))) keeps only v, matching sample.
TEST(LocalVariableFlow, FlowThroughNestedLocalDeclHidesOuterDeclaredName) {
  auto inner = SeqConcat(Samp("w"), Samp("v"));
  auto seq = SeqLocalVarDecl("int", "w", inner);
  EXPECT_EQ(FlowLocals({}, *seq), (NameSet{"v"}));
  EXPECT_EQ(SampleLocals(*seq), (NameSet{"v"}));
}

// §F.5.4 edge case for block((R1 ##1 R2)) = (block(R1) - flow({}, R2)) U
// block(R2): when R2 is a Boolean it flows nothing, so no name is subtracted
// and the left operand's blocked set is retained in full.
TEST(LocalVariableFlow, BlockOfConcatRetainsLeftBlockWhenRightFlowsNothing) {
  EXPECT_EQ(BlockLocals(*SeqConcat(BlockOf("v"), Bool())), (NameSet{"v"}));
}

// §F.5.4 edge case for flow(X, (R1 intersect R2)) =
// (flow(X, R1) U flow(X, R2)) - block((R1 intersect R2)): the block term
// subtracts a commonly sampled name even when it arrived in the input set.
TEST(LocalVariableFlow, FlowThroughIntersectRemovesIncomingBlockedName) {
  EXPECT_EQ(FlowLocals({"v"}, *SeqIntersect(Samp("v"), Samp("v"))), NameSet{});
}

// §F.5.4 edge case for block((R1 intersect R2)) =
// block(R1) U block(R2) U (sample(R1) ∩ sample(R2)): all three contributions
// appear together -- each operand's own block plus the name sampled in both.
TEST(LocalVariableFlow, BlockOfIntersectCombinesOperandBlocksAndCommonSamples) {
  auto left = SeqConcat(Samp("v"), BlockOf("x"));   // blocks {x}, samples {v,x}
  auto right = SeqConcat(Samp("v"), BlockOf("y"));  // blocks {y}, samples {v,y}
  EXPECT_EQ(BlockLocals(*SeqIntersect(left, right)), (NameSet{"v", "x", "y"}));
}

}  // namespace
