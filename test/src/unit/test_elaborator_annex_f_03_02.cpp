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
  const auto kForms = ProductionForms(GrammarProduction::kClockedSequence);
  ASSERT_FALSE(kForms.empty());
  EXPECT_EQ(kForms.front().operands, (std::vector<std::string>{"b", "R"}));
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

// §F.3.2: the clocked property production Q mirrors P but begins with the
// clock form and threads the clocked sequence S through its sequence forms.
TEST(AbstractGrammar, ClockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedProperty),
            (std::vector<std::string>{
                "clock", "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

// §F.3.2: the implication form of Q is ( S |-> Q ) -- unlike P's ( R |-> P ),
// its antecedent is a clocked sequence S and its consequent a clocked property
// Q. This pins the clocked counterpart of the unclocked implication operands.
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

// §F.3.2: the assertion operands encode the clocked/unclocked split of the
// bodies. The unclocked always/initial forms take a clocked top-level property
// U; the "with clock" forms take a Boolean clock b over an unclocked top-level
// property T. This observes the RHS operand shapes, not just the form labels.
TEST(AbstractGrammar, AssertionFormOperandsDistinguishClockedBodies) {
  const auto kForms = ProductionForms(GrammarProduction::kAssertion);
  ASSERT_EQ(kForms.size(), 4u);
  EXPECT_EQ(kForms[0].operands, (std::vector<std::string>{"U"}));  // always
  EXPECT_EQ(kForms[1].operands,
            (std::vector<std::string>{"b", "T"}));  // always with clock
  EXPECT_EQ(kForms[2].operands, (std::vector<std::string>{"U"}));  // initial
  EXPECT_EQ(kForms[3].operands,
            (std::vector<std::string>{"b", "T"}));  // initial with clock
}

// §F.3.2's productions are named by the §F.3.3 metavariable conventions: each
// production carries exactly the category §F.3.3 assigns to its letter. This
// ties the abstract grammar to the notation that describes it.
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

// §F.3.2 cites §F.5.5 as well as §F.5.2 for the definitions of nondegeneracy
// and tight satisfaction. A sequence operand that samples a local variable,
// ( 1, v = e ), admits a one-letter match and never the empty word, so it is a
// nondegenerate operand. §F.5.2 does not model the sampling form, so only the
// §F.5.5 definition classifies it correctly -- and the requirement check must
// consult that definition to accept the operand.
TEST(AbstractGrammar, NondegenerateLocalVariableSamplingOperandIsAccepted) {
  auto sampling = SeqLocalVarSampling("v");
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*sampling));
}

// §F.3.2 (via §F.5.5): a local-variable operand that admits only the empty
// match is still degenerate. ( t v; a[*0] ) declares v over a null repetition,
// whose body matches only the empty word, so no nonempty word satisfies it and
// it is rejected.
TEST(AbstractGrammar, DegenerateLocalVariableOperandIsRejected) {
  auto empty_only =
      SeqLocalVarDecl("int", "v", SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

// §F.3.2 (via §F.5.5): even a nondegenerate local-variable operand is rejected
// when it can also be tightly satisfied by the empty word. ( a[*0] or (1, v=e)
// ) admits a one-letter match through the sampling branch yet also matches the
// empty word through the null-repetition branch, so the empty-word clause
// rejects it -- and only the §F.5.5 tight-satisfaction relation, which models
// the sampling branch, evaluates this operand.
TEST(AbstractGrammar, LocalVariableOperandMatchingEmptyWordIsRejected) {
  auto admits_empty_too =
      SeqOr(SeqNullRepeat(SeqBoolean(BoolAtom("a"))), SeqLocalVarSampling("v"));
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

}  // namespace
