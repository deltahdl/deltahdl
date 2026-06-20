#include <gtest/gtest.h>

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

// §F.3.2: the unclocked sequence production R lists eleven alternatives, from
// the bare Boolean through the two repetition forms.
TEST(AbstractGrammar, UnclockedSequenceProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedSequence),
      (std::vector<std::string>{
          "boolean", "local variable declaration", "local variable sampling",
          "parenthesis", "concatenation", "fusion", "or", "intersect",
          "first match", "null repetition", "unbounded repetition"}));
}

// §F.3.2: the clocked sequence production S adds the clock form and keeps only
// the declaration, parenthesis, and concatenation structural forms.
TEST(AbstractGrammar, ClockedSequenceProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedSequence),
            (std::vector<std::string>{"clock", "local variable declaration",
                                      "parenthesized", "concatenation"}));
}

// §F.3.2: the clock form of S is @( b ) R -- a Boolean guard over an unclocked
// sequence.
TEST(AbstractGrammar, ClockedSequenceClockFormOperands) {
  const auto forms = ProductionForms(GrammarProduction::kClockedSequence);
  ASSERT_FALSE(forms.empty());
  EXPECT_EQ(forms.front().operands, (std::vector<std::string>{"b", "R"}));
}

// §F.3.2: the unclocked property production P opens with the strong and weak
// sequence forms and closes with the abort form.
TEST(AbstractGrammar, UnclockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kUnclockedProperty),
            (std::vector<std::string>{
                "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

// §F.3.2: the implication form of P is ( R |-> P ): an unclocked sequence
// antecedent and an unclocked property consequent.
TEST(AbstractGrammar, UnclockedPropertyImplicationOperands) {
  const auto forms = ProductionForms(GrammarProduction::kUnclockedProperty);
  bool found = false;
  for (const auto& form : forms) {
    if (form.label == "implication") {
      found = true;
      EXPECT_EQ(form.operands, (std::vector<std::string>{"R", "P"}));
    }
  }
  EXPECT_TRUE(found);
}

// §F.3.2: the clocked property production Q mirrors P but begins with the
// clock form and threads the clocked sequence S through its sequence forms.
TEST(AbstractGrammar, ClockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedProperty),
            (std::vector<std::string>{
                "clock", "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

// §F.3.2: the unclocked top-level property T is a plain property, a
// disable-iff guarded property, a declaration, or a parenthesized form.
TEST(AbstractGrammar, UnclockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

// §F.3.2: the clocked top-level property U has the same four shapes as T but
// over the clocked property Q.
TEST(AbstractGrammar, ClockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kClockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

// §F.3.2: an assertion A is an always/initial assertion, either with an
// explicit clock over a T body or unclocked over a U body.
TEST(AbstractGrammar, AssertionProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kAssertion),
            (std::vector<std::string>{"always", "always with clock", "initial",
                                      "initial with clock"}));
}

// §F.3.2's productions are named by the §F.3.3 metavariable conventions: each
// production carries exactly the category §F.3.3 assigns to its letter. This
// ties the abstract grammar to the notation that describes it.
TEST(AbstractGrammar, ProductionCategoriesMatchNotation) {
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedSequence),
            ClassifyAnnexFNotation("R").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedSequence),
            ClassifyAnnexFNotation("S").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedProperty),
            ClassifyAnnexFNotation("P").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedProperty),
            ClassifyAnnexFNotation("Q").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedTopLevelProperty),
            ClassifyAnnexFNotation("T").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedTopLevelProperty),
            ClassifyAnnexFNotation("U").value());
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kAssertion),
            ClassifyAnnexFNotation("A").value());
}

// §F.3.2: each R form is representable in the shared sequence model and keeps
// its distinguishing kind, which the rewrite (§F.5.1.1) and tight-satisfaction
// (§F.5.2) passes dispatch on.
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

// §F.3.2: S is exactly R with a clock form. A sequence is clocked precisely
// when the @( b ) form occurs within it.
TEST(AbstractGrammar, ClockFormDistinguishesClockedSequences) {
  auto unclocked =
      SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_FALSE(ContainsClock(*unclocked));

  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ContainsClock(*clocked));

  auto nested = SeqConcat(SeqBoolean(BoolAtom("a")), clocked);
  EXPECT_TRUE(ContainsClock(*nested));
}

// §F.3.2: in the strong/weak "sequence" forms of P, the sequence operand shall
// be nondegenerate. A plain Boolean admits a one-letter match and never the
// empty word, so it meets the requirement.
TEST(AbstractGrammar, NondegenerateSequenceOperandIsAccepted) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*b));
}

// §F.3.2: a sequence that admits only the empty match (R[*0]) is degenerate
// and is rejected as a strong/weak sequence operand.
TEST(AbstractGrammar, EmptyOnlySequenceOperandIsRejected) {
  auto empty_only = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

// §F.3.2: even a nondegenerate sequence is rejected as a strong/weak operand
// when it can also be tightly satisfied by the empty word -- the production
// forbids the empty match outright. (b or b[*0]) admits a one-letter match
// yet also matches the empty word.
TEST(AbstractGrammar, SequenceOperandMatchingEmptyWordIsRejected) {
  auto b = SeqBoolean(BoolAtom("a"));
  auto admits_empty_too = SeqOr(SeqNullRepeat(b), b);
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

// §F.3.2: the clocked property production Q carries the same requirement for
// its sequence operand S -- "each instance of S ... shall be a nondegenerate
// clocked sequence". A clocked Boolean @(clk) a admits a one-letter match
// (and not the empty word), so it meets the requirement on a clocked operand.
TEST(AbstractGrammar, NondegenerateClockedSequenceOperandIsAccepted) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

// §F.3.2: Q's "sequence" form also forbids a clocked operand that admits only
// the empty match. @(clk) (a[*0]) reduces to a clocked null repetition, which
// is degenerate and tightly satisfied by the empty word, so it is rejected.
TEST(AbstractGrammar, DegenerateClockedSequenceOperandIsRejected) {
  auto clocked =
      SeqClock(BoolAtom("clk"), SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

}  // namespace
