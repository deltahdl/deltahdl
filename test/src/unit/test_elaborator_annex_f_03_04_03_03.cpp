#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

TEST(DerivedNonoverlappingImplication, UnclockedFormLengthensTheAntecedent) {
  auto p = PropStrong(Atom("b"));
  auto form = PropNonoverlappingImplication(Atom("a"), p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->sequence,
                                *SeqConcat(Atom("a"), SeqBoolean(BoolTrue()))));
  EXPECT_EQ(form->lhs, p);
}

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
