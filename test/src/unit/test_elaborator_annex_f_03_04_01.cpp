#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const AssertionStatement> AlwaysStrongA(
    AssertionStatement::Role role) {
  return AssertionWithClock(AssertionStatement::Activation::kAlways, role,
                            BoolAtom("clk"),
                            TopProperty(PropStrong(SeqBoolean(BoolAtom("a")))));
}

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
