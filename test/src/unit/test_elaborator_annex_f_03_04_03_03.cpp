#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4.3.3 unfolds the nonoverlapping implication into the §F.3.2
// overlapping one over an antecedent lengthened by one letter: (R |=> P) is
// ((R ##1 1) |-> P) over an unclocked sequence, and (S |=> Q) is
// ((S ##1 @(1) 1) |-> Q) over a clocked one. The cases check that each
// factory builds the tree its identity names and that, under §F.5.3.1, the
// consequent is judged from the letter after the antecedent's match where the
// overlapping form judges it from the letter the match ends at.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

// The unclocked form is the implication whose antecedent is (R ##1 1) and
// whose consequent is P itself.
TEST(DerivedNonoverlappingImplication, UnclockedFormLengthensTheAntecedent) {
  auto p = PropStrong(Atom("b"));
  auto form = PropNonoverlappingImplication(Atom("a"), p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->sequence,
                                *SeqConcat(Atom("a"), SeqBoolean(BoolTrue()))));
  EXPECT_EQ(form->lhs, p);
}

// The clocked form's antecedent ends in the clocked constant @(1) 1 rather
// than the bare constant, which is what parts it from the unclocked form.
TEST(DerivedNonoverlappingImplication, ClockedFormClocksTheAddedLetter) {
  auto q = ClkStrong(Atom("b"));
  auto s = SeqClock(BoolAtom("clk"), Atom("a"));
  auto clocked_one = SeqClock(BoolTrue(), SeqBoolean(BoolTrue()));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkNonoverlappingImplication(s, q),
                           *ClkImplication(SeqConcat(s, clocked_one), q)));
  EXPECT_FALSE(ClockedPropertyEqual(
      *ClkNonoverlappingImplication(s, q),
      *ClkImplication(SeqConcat(s, SeqBoolean(BoolTrue())), q)));
}

// Under §F.5.3.1, a |=> strong(b) needs b on the letter after a: it holds on
// a then b, fails on a then a letter without b, and holds vacuously on a lone
// a, whose one letter is too short for the antecedent. The overlapping
// a |-> strong(b) needs b on the letter with a, so it fails on a then b and
// holds on a and b together followed by anything.
TEST(DerivedNonoverlappingImplication, TheConsequentStartsOneLetterLater) {
  auto nonoverlapping =
      PropNonoverlappingImplication(Atom("a"), PropStrong(Atom("b")));
  auto overlapping = PropImplication(Atom("a"), PropStrong(Atom("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *nonoverlapping));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *overlapping));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *nonoverlapping));
  EXPECT_FALSE(
      NeutrallySatisfies(Word{A({"a", "b"}), A({"x"})}, *nonoverlapping));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"}), A({"x"})}, *overlapping));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *nonoverlapping));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"x"})}, *nonoverlapping));
}

// In the clocked model under @(clk), the added letter is one letter of the
// word and the consequent then waits for the next clk tick: a at one tick
// followed by an unclocked letter and then b at the next tick satisfies
// a |=> strong(b) where the overlapping form, judged from the letter with a,
// does not; b absent at the next tick fails both.
TEST(DerivedNonoverlappingImplication, UnderAClockTheConsequentWaitsATick) {
  auto clk = BoolAtom("clk");
  auto nonoverlapping = ClkClock(
      clk, ClkNonoverlappingImplication(Atom("a"), ClkStrong(Atom("b"))));
  auto overlapping =
      ClkClock(clk, ClkImplication(Atom("a"), ClkStrong(Atom("b"))));
  const Word kNextTickHasB{A({"clk", "a"}), A({"x"}), A({"clk", "b"})};
  const Word kNextTickLacksB{A({"clk", "a"}), A({"x"}), A({"clk", "x"})};
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(kNextTickHasB, *nonoverlapping));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kNextTickHasB, *overlapping));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kNextTickLacksB, *nonoverlapping));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kNextTickLacksB, *overlapping));
}

}  // namespace
