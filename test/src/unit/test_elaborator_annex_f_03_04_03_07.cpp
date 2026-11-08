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

TEST(DerivedAbortOperators, UnclockedSyncRejectOnAgreesWithRejectOn) {
  auto p = PropNot(PropStrong(Atom("c")));
  auto sync_reject = PropSyncRejectOn(BoolAtom("r"), p);
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"r"})}, *sync_reject));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"r"})}, *sync_reject));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"c"})}, *sync_reject));
}

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
