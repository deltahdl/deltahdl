#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4.1 has one derived assertion statement: restrict property stands for
// assume property. The §F.3.2 assertion production knows three roles, and the
// fourth directive of §16.14 reaches the semantics through this identity.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// An always statement of the given role over the body strong(a) clocked on
// clk.
std::shared_ptr<const AssertionStatement> AlwaysStrongA(
    AssertionStatement::Role role) {
  return AssertionWithClock(AssertionStatement::Activation::kAlways, role,
                            BoolAtom("clk"),
                            TopProperty(PropStrong(SeqBoolean(BoolAtom("a")))));
}

// §F.3.4.1: the restrict directive takes the assume role; the three
// directives §F.3.2 names take their own.
TEST(DerivedAssertionStatement, RestrictIsTheAssumeRole) {
  EXPECT_EQ(RoleOfConcurrentAssertionDirective(
                ConcurrentAssertionDirective::kRestrict),
            AssertionStatement::Role::kAssume);
  EXPECT_EQ(
      RoleOfConcurrentAssertionDirective(ConcurrentAssertionDirective::kAssume),
      AssertionStatement::Role::kAssume);
  EXPECT_EQ(
      RoleOfConcurrentAssertionDirective(ConcurrentAssertionDirective::kAssert),
      AssertionStatement::Role::kAssert);
  EXPECT_EQ(
      RoleOfConcurrentAssertionDirective(ConcurrentAssertionDirective::kCover),
      AssertionStatement::Role::kCover);
}

// §F.3.4.1 with §F.5.3.1: a restrict statement is neutrally satisfied by the
// words its assume statement is, which are the words the assert statement is
// -- every clock tick with a, or no tick at all -- and not by the words a
// cover statement is, which needs one such tick and holds where a later tick
// lacks a.
TEST(DerivedAssertionStatement, RestrictIsSatisfiedAsAssume) {
  auto restrict_stmt = AlwaysStrongA(RoleOfConcurrentAssertionDirective(
      ConcurrentAssertionDirective::kRestrict));
  auto assume_stmt = AlwaysStrongA(AssertionStatement::Role::kAssume);
  auto cover_stmt = AlwaysStrongA(AssertionStatement::Role::kCover);
  const Word kEveryTickHasA{A({"clk", "a"}), A({"clk", "a"})};
  const Word kSecondTickLacksA{A({"clk", "a"}), A({"clk"})};
  const Word kNoTick{A({"x"})};
  for (const Word& w : {kEveryTickHasA, kSecondTickLacksA, kNoTick}) {
    EXPECT_EQ(NeutrallySatisfiesAssertion(w, *BoolTrue(), *restrict_stmt),
              NeutrallySatisfiesAssertion(w, *BoolTrue(), *assume_stmt));
  }
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(kEveryTickHasA, *BoolTrue(), *restrict_stmt));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(kSecondTickLacksA, *BoolTrue(),
                                           *restrict_stmt));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(kNoTick, *BoolTrue(), *restrict_stmt));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(kSecondTickLacksA, *BoolTrue(), *cover_stmt));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(kNoTick, *BoolTrue(), *cover_stmt));
}

}  // namespace
