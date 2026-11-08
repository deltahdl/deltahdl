#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_notation.h"

using namespace delta;

namespace {

std::vector<std::string> Labels(GrammarProduction production) {
  std::vector<std::string> labels;
  for (const auto& form : ProductionForms(production)) {
    labels.push_back(form.label);
  }
  return labels;
}

TEST(AbstractGrammar, UnclockedSequenceProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedSequence),
      (std::vector<std::string>{
          "boolean", "local variable declaration", "local variable sampling",
          "parenthesis", "concatenation", "fusion", "or", "intersect",
          "first match", "null repetition", "unbounded repetition"}));
}

TEST(AbstractGrammar, ClockedSequenceProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedSequence),
            (std::vector<std::string>{"clock", "local variable declaration",
                                      "parenthesized", "concatenation"}));
}

TEST(AbstractGrammar, ClockedSequenceClockFormOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kClockedSequence);
  ASSERT_FALSE(kForms.empty());
  EXPECT_EQ(kForms.front().operands, (std::vector<std::string>{"b", "R"}));
}

TEST(AbstractGrammar, UnclockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kUnclockedProperty),
            (std::vector<std::string>{
                "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

TEST(AbstractGrammar, UnclockedPropertyImplicationOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kUnclockedProperty);
  bool found = false;
  for (const auto& form : kForms) {
    if (form.label == "implication") {
      found = true;
      EXPECT_EQ(form.operands, (std::vector<std::string>{"R", "P"}));
    }
  }
  EXPECT_TRUE(found);
}

TEST(AbstractGrammar, ClockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedProperty),
            (std::vector<std::string>{
                "clock", "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

TEST(AbstractGrammar, ClockedPropertyImplicationOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kClockedProperty);
  bool found = false;
  for (const auto& form : kForms) {
    if (form.label == "implication") {
      found = true;
      EXPECT_EQ(form.operands, (std::vector<std::string>{"S", "Q"}));
    }
  }
  EXPECT_TRUE(found);
}

TEST(AbstractGrammar, UnclockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

TEST(AbstractGrammar, ClockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kClockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

TEST(AbstractGrammar, AssertionProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kAssertion),
            (std::vector<std::string>{"always", "always with clock", "initial",
                                      "initial with clock"}));
}

TEST(AbstractGrammar, AssertionFormOperandsDistinguishClockedBodies) {
  const auto kForms = ProductionForms(GrammarProduction::kAssertion);
  ASSERT_EQ(kForms.size(), 4u);
  EXPECT_EQ(kForms[0].operands, (std::vector<std::string>{"U"}));
  EXPECT_EQ(kForms[1].operands, (std::vector<std::string>{"b", "T"}));
  EXPECT_EQ(kForms[2].operands, (std::vector<std::string>{"U"}));
  EXPECT_EQ(kForms[3].operands, (std::vector<std::string>{"b", "T"}));
}

TEST(AbstractGrammar, ProductionCategoriesMatchNotation) {
  const auto kRCategory = ClassifyAnnexFNotation("R");
  ASSERT_TRUE(kRCategory.has_value());
  if (!kRCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedSequence),
            *kRCategory);
  const auto kSCategory = ClassifyAnnexFNotation("S");
  ASSERT_TRUE(kSCategory.has_value());
  if (!kSCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedSequence),
            *kSCategory);
  const auto kPCategory = ClassifyAnnexFNotation("P");
  ASSERT_TRUE(kPCategory.has_value());
  if (!kPCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedProperty),
            *kPCategory);
  const auto kQCategory = ClassifyAnnexFNotation("Q");
  ASSERT_TRUE(kQCategory.has_value());
  if (!kQCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedProperty),
            *kQCategory);
  const auto kTCategory = ClassifyAnnexFNotation("T");
  ASSERT_TRUE(kTCategory.has_value());
  if (!kTCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedTopLevelProperty),
            *kTCategory);
  const auto kUCategory = ClassifyAnnexFNotation("U");
  ASSERT_TRUE(kUCategory.has_value());
  if (!kUCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedTopLevelProperty),
            *kUCategory);
  const auto kACategory = ClassifyAnnexFNotation("A");
  ASSERT_TRUE(kACategory.has_value());
  if (!kACategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kAssertion), *kACategory);
}

TEST(AbstractGrammar, SequenceModelRepresentsUnclockedForms) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_EQ(b->kind, SequenceExpr::Kind::kBoolean);
  EXPECT_EQ(SeqParen(b)->kind, SequenceExpr::Kind::kParen);
  EXPECT_EQ(SeqConcat(b, b)->kind, SequenceExpr::Kind::kConcat);
  EXPECT_EQ(SeqFusion(b, b)->kind, SequenceExpr::Kind::kFusion);
  EXPECT_EQ(SeqOr(b, b)->kind, SequenceExpr::Kind::kOr);
  EXPECT_EQ(SeqIntersect(b, b)->kind, SequenceExpr::Kind::kIntersect);
  EXPECT_EQ(SeqFirstMatch(b)->kind, SequenceExpr::Kind::kFirstMatch);
  EXPECT_EQ(SeqNullRepeat(b)->kind, SequenceExpr::Kind::kNullRepeat);
  EXPECT_EQ(SeqUnboundedRepeat(b)->kind, SequenceExpr::Kind::kUnboundedRepeat);
  EXPECT_EQ(SeqLocalVarSampling("v")->kind,
            SequenceExpr::Kind::kLocalVarSampling);
  EXPECT_EQ(SeqLocalVarDecl("int", "v", b)->kind,
            SequenceExpr::Kind::kLocalVarDecl);
}

TEST(AbstractGrammar, ClockFormDistinguishesClockedSequences) {
  auto unclocked =
      SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_FALSE(ContainsClock(*unclocked));

  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ContainsClock(*clocked));

  auto nested = SeqConcat(SeqBoolean(BoolAtom("a")), clocked);
  EXPECT_TRUE(ContainsClock(*nested));
}

TEST(AbstractGrammar, NondegenerateSequenceOperandIsAccepted) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*b));
}

TEST(AbstractGrammar, EmptyOnlySequenceOperandIsRejected) {
  auto empty_only = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

TEST(AbstractGrammar, SequenceOperandMatchingEmptyWordIsRejected) {
  auto b = SeqBoolean(BoolAtom("a"));
  auto admits_empty_too = SeqOr(SeqNullRepeat(b), b);
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

TEST(AbstractGrammar, NondegenerateClockedSequenceOperandIsAccepted) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

TEST(AbstractGrammar, DegenerateClockedSequenceOperandIsRejected) {
  auto clocked =
      SeqClock(BoolAtom("clk"), SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

TEST(AbstractGrammar, NondegenerateLocalVariableSamplingOperandIsAccepted) {
  auto sampling = SeqLocalVarSampling("v");
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*sampling));
}

TEST(AbstractGrammar, DegenerateLocalVariableOperandIsRejected) {
  auto empty_only =
      SeqLocalVarDecl("int", "v", SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

TEST(AbstractGrammar, LocalVariableOperandMatchingEmptyWordIsRejected) {
  auto admits_empty_too =
      SeqOr(SeqNullRepeat(SeqBoolean(BoolAtom("a"))), SeqLocalVarSampling("v"));
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

}  // namespace
