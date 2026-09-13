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

// §F.3.4.3.7 unfolds the derived abort operators into the §F.3.2 accept_on
// form and negation: (reject_on(b) P) is (not accept_on(b) not P),
// (sync_accept_on(b) P) is (accept_on(b) P) when the clock context is 1, and
// (sync_reject_on(b) P) is (not (sync_accept_on(b) not P)). The cases check
// that each factory builds the tree its identity names in both property
// models, that the synchronous accept is the plain one in the unclocked model
// and only there, and that, under §F.5.3.1, a reject_on fails where an abort
// letter completes the word into one P fails on, though P holds on the word.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

// reject_on(b) P is the negation of accept_on(b) over the negation of P: the
// outer node is a not whose operand is the accept_on carrying b, and that
// accept_on's operand is a not over P itself.
TEST(DerivedAbortOperators, RejectOnNegatesTheAcceptOnOfTheNegation) {
  auto b = BoolAtom("r");
  auto p = PropStrong(Atom("c"));
  auto form = PropRejectOn(b, p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, PropertyExpr::Kind::kAcceptOn);
  EXPECT_EQ(form->lhs->boolean, b);
  ASSERT_NE(form->lhs->lhs, nullptr);
  ASSERT_EQ(form->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(form->lhs->lhs->lhs, p);
}

// In the unclocked model the clock context is 1, so sync_accept_on(b) P is
// the accept_on(b) P node itself, and sync_reject_on(b) P is therefore the
// same tree as reject_on(b) P.
TEST(DerivedAbortOperators, UnclockedSyncFormsAreThePlainForms) {
  auto b = BoolAtom("r");
  auto p = PropStrong(Atom("c"));
  auto sync_accept = PropSyncAcceptOn(b, p);
  ASSERT_EQ(sync_accept->kind, PropertyExpr::Kind::kAcceptOn);
  EXPECT_EQ(sync_accept->boolean, b);
  EXPECT_EQ(sync_accept->lhs, p);
  auto sync_reject = PropSyncRejectOn(b, p);
  ASSERT_EQ(sync_reject->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(sync_reject->lhs, nullptr);
  ASSERT_EQ(sync_reject->lhs->kind, PropertyExpr::Kind::kAcceptOn);
  EXPECT_EQ(sync_reject->lhs->boolean, b);
  ASSERT_NE(sync_reject->lhs->lhs, nullptr);
  ASSERT_EQ(sync_reject->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(sync_reject->lhs->lhs->lhs, p);
}

// The clocked forms are the stated trees over the §F.5.1.2 abort nodes: the
// reject_on negates an accept_on over the negation, the sync_reject_on
// negates a sync_accept_on over the negation, and the two differ because the
// synchronous abort is its own node under a clock.
TEST(DerivedAbortOperators, ClockedFormsAreTheStatedTrees) {
  auto b = BoolAtom("r");
  auto q = ClkStrong(Atom("c"));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkRejectOn(b, q),
                                   *ClkNot(ClkAcceptOn(b, ClkNot(q)))));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkSyncRejectOn(b, q),
                                   *ClkNot(ClkSyncAcceptOn(b, ClkNot(q)))));
  EXPECT_FALSE(
      ClockedPropertyEqual(*ClkRejectOn(b, q), *ClkSyncRejectOn(b, q)));
  EXPECT_FALSE(
      ClockedPropertyEqual(*ClkRejectOn(b, q), *ClkAcceptOn(b, ClkNot(q))));
}

// Under §F.5.3.1, reject_on(r) (not strong(c)) holds on a letter without c or
// r, fails on a letter with c where the property fails outright, and fails on
// a lone r though the property holds there: the abort at r completes the
// empty prefix with the top letter, on which strong(c) holds and its negation
// fails. On a letter without c followed by r it holds, because the first
// letter already decides the negation before the abort. The accept_on over
// the same property holds on the lone r, which is what parts the two.
TEST(DerivedAbortOperators, RejectOnFailsWhereAnAbortCompletionFailsP) {
  auto p = PropNot(PropStrong(Atom("c")));
  auto reject = PropRejectOn(BoolAtom("r"), p);
  auto accept = PropAcceptOn(BoolAtom("r"), p);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"})}, *reject));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"c"})}, *reject));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"r"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"r"})}, *reject));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"r"})}, *accept));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"r"})}, *reject));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"c"}), A({"r"})}, *reject));
}

// The unclocked sync_reject_on gives the reject_on's verdicts, since the
// clock context is 1 there: it fails on the lone r and holds on a letter
// without c followed by r.
TEST(DerivedAbortOperators, UnclockedSyncRejectOnAgreesWithRejectOn) {
  auto p = PropNot(PropStrong(Atom("c")));
  auto sync_reject = PropSyncRejectOn(BoolAtom("r"), p);
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"r"})}, *sync_reject));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"r"})}, *sync_reject));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"c"})}, *sync_reject));
}

// In the clocked model with the clock context 1, sync_accept_on(r) strong(c)
// and accept_on(r) strong(c) agree letter for letter: both hold on c, both
// hold on a lone r through the abort's completion, and both fail on a letter
// with neither. Under @(clk) they part: the synchronous abort is sampled with
// the clock, so r on an unclocked letter aborts the plain form and not the
// synchronous one, whose strong(c) then fails at the tick without c.
TEST(DerivedAbortOperators, SyncAcceptOnIsAcceptOnOnlyInClockContextOne) {
  auto r = BoolAtom("r");
  auto q = ClkStrong(Atom("c"));
  auto sync_accept = ClkSyncAcceptOn(r, q);
  auto accept = ClkAcceptOn(r, q);
  for (const Word& word : {Word{A({"c"})}, Word{A({"r"})}, Word{A({"x"})},
                           Word{A({"x"}), A({"r"})}}) {
    EXPECT_EQ(NeutrallySatisfiesClockedProperty(word, *sync_accept),
              NeutrallySatisfiesClockedProperty(word, *accept));
  }
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(Word{A({"r"})}, *sync_accept));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"x"})}, *sync_accept));

  auto clk = BoolAtom("clk");
  const Word kUnclockedAbort{A({"r"}), A({"clk", "x"})};
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kUnclockedAbort,
                                                *ClkClock(clk, accept)));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kUnclockedAbort,
                                                 *ClkClock(clk, sync_accept)));
  const Word kClockedAbort{A({"clk", "r"}), A({"clk", "x"})};
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kClockedAbort,
                                                *ClkClock(clk, sync_accept)));
}

// The clocked reject_on and sync_reject_on give the reject_on verdicts of the
// unclocked model when the clock context is 1, and under @(clk) part the same
// way the accepts do: r on an unclocked letter is an abort for the plain
// reject_on, whose completion then fails not strong(c) at the tick, and not
// for the synchronous one, which the tick without c decides in favour of.
TEST(DerivedAbortOperators, ClockedRejectsPartUnderAClockAsTheAcceptsDo) {
  auto r = BoolAtom("r");
  auto q = ClkNot(ClkStrong(Atom("c")));
  auto reject = ClkRejectOn(r, q);
  auto sync_reject = ClkSyncRejectOn(r, q);
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"r"})}, *reject));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"r"})}, *sync_reject));
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"r"})}, *reject));
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"r"})},
                                                *sync_reject));

  auto clk = BoolAtom("clk");
  const Word kUnclockedAbort{A({"r"}), A({"clk", "x"})};
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kUnclockedAbort,
                                                 *ClkClock(clk, reject)));
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kUnclockedAbort,
                                                *ClkClock(clk, sync_reject)));
}

}  // namespace
