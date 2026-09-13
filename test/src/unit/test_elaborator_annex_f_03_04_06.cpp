#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4.6 unfolds the two free checker variable assignments into assume
// property statements: rand t u = e is initial assume property (@1 u === e),
// and always_ff @c u <= e is always_ff assume property (@1 $future_gclk(u)
// === (c ? e : u)). The Boolean each compares is outside the §F.3.2 Boolean
// model, so the caller supplies it and the cases stand it in by an atom. The
// cases check that each factory builds the statement its identity names --
// the role, the activation, the @1 clock form and the weak reading of the
// bare Boolean -- that the caller's Boolean is asked about the name and the
// clock given, and that, under §F.5.3.1, the rand form constrains the first
// letter alone where the always_ff form constrains every letter.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// The Boolean u === e stands in as the atom eq_<u>, and the Boolean
// $future_gclk(u) === (c ? e : u) as the atom next_<u>_<c>, so a letter says
// whether the comparison holds.
std::shared_ptr<const BooleanExpr> Equality(const std::string& u) {
  return BoolAtom("eq_" + u);
}
std::shared_ptr<const BooleanExpr> NextValue(
    const std::string& u, const std::shared_ptr<const BooleanExpr>& c) {
  return BoolAtom("next_" + u + "_" + c->atom);
}

// The body both statements share: @(1) weak(b) as a clocked top-level
// property, which is what the unfolding wraps the caller's Boolean in.
void ExpectBodyIsWeakAtGlobalClock(const AssertionStatement& statement,
                                   const std::string& atom) {
  ASSERT_EQ(statement.form, AssertionStatement::Form::kClockedTop);
  ASSERT_NE(statement.clocked_top, nullptr);
  EXPECT_EQ(statement.top, nullptr);
  EXPECT_EQ(statement.clock, nullptr);
  ASSERT_EQ(statement.clocked_top->kind,
            ClockedTopLevelProperty::Kind::kProperty);
  ASSERT_NE(statement.clocked_top->property, nullptr);
  EXPECT_TRUE(ClockedPropertyEqual(
      *statement.clocked_top->property,
      *ClkClock(BoolTrue(), ClkWeak(SeqBoolean(BoolAtom(atom))))));
  EXPECT_FALSE(ClockedPropertyEqual(
      *statement.clocked_top->property,
      *ClkClock(BoolTrue(), ClkStrong(SeqBoolean(BoolAtom(atom))))));
}

// rand t u = e is an initial assume property statement whose body is @1 over
// the weak reading of u === e.
TEST(DerivedFreeCheckerAssignments, RandAssignmentIsAnInitialAssume) {
  auto statement = FreeCheckerRandAssignment("u", Equality);
  EXPECT_EQ(statement->activation, AssertionStatement::Activation::kInitial);
  EXPECT_EQ(statement->role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(*statement, "eq_u");
}

// always_ff @c u <= e is an always assume property statement whose body is
// @1 over the weak reading of $future_gclk(u) === (c ? e : u).
TEST(DerivedFreeCheckerAssignments, AlwaysFfAssignmentIsAnAlwaysAssume) {
  auto statement = FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue);
  EXPECT_EQ(statement->activation, AssertionStatement::Activation::kAlways);
  EXPECT_EQ(statement->role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(*statement, "next_u_c");
}

// The caller's Boolean is asked about the name given, and for the always_ff
// form about the clock given as well, once per statement.
TEST(DerivedFreeCheckerAssignments, TheBooleanIsAskedAboutTheNameAndClock) {
  std::vector<std::string> names;
  std::vector<std::shared_ptr<const BooleanExpr>> clocks;
  const FreeCheckerEquality kRecordingEquality =
      [&names](const std::string& u) {
        names.push_back(u);
        return Equality(u);
      };
  const FreeCheckerNextValue kRecordingNextValue =
      [&names, &clocks](const std::string& u,
                        const std::shared_ptr<const BooleanExpr>& c) {
        names.push_back(u);
        clocks.push_back(c);
        return NextValue(u, c);
      };
  FreeCheckerRandAssignment("v", kRecordingEquality);
  ASSERT_EQ(names.size(), 1U);
  EXPECT_EQ(names[0], "v");
  EXPECT_TRUE(clocks.empty());
  auto c = BoolAtom("c");
  FreeCheckerAlwaysFfAssignment("w", c, kRecordingNextValue);
  ASSERT_EQ(names.size(), 2U);
  EXPECT_EQ(names[1], "w");
  ASSERT_EQ(clocks.size(), 1U);
  EXPECT_EQ(clocks[0], c);
}

// Under §F.5.3.1, the rand form is judged at the first letter alone, since
// the global clock ticks on every letter and the initial form fires at the
// first tick: it holds where eq_u is on the first letter whatever follows,
// and fails where the first letter lacks it though a later one has it.
TEST(DerivedFreeCheckerAssignments, TheRandFormConstrainsTheFirstLetter) {
  auto statement = FreeCheckerRandAssignment("u", Equality);
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"eq_u"}), A({"x"})},
                                          *BoolTrue(), *statement));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"eq_u"})}, *BoolTrue(), *statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"eq_u"})},
                                           *BoolTrue(), *statement));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *statement));
}

// Under §F.5.3.1, the always_ff form is judged at every letter: it holds
// where next_u_c is on each letter and fails where any letter lacks it, so a
// word the rand form of the same atom accepts is one it rejects.
TEST(DerivedFreeCheckerAssignments, TheAlwaysFfFormConstrainsEveryLetter) {
  auto statement = FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue);
  EXPECT_TRUE(NeutrallySatisfiesAssertion(
      Word{A({"next_u_c"}), A({"next_u_c"})}, *BoolTrue(), *statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"next_u_c"}), A({"x"})},
                                           *BoolTrue(), *statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"next_u_c"})},
                                           *BoolTrue(), *statement));
  auto rand_of_same_atom = FreeCheckerRandAssignment(
      "u", [](const std::string& u) { return BoolAtom("next_" + u + "_c"); });
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"next_u_c"}), A({"x"})},
                                          *BoolTrue(), *rand_of_same_atom));
}

// Both statements are assumptions, so under §F.5.3.1 a word is feasible
// under them iff each is satisfied on it: with both in force, a word with
// eq_u on the first letter and next_u_c on every letter is feasible, one
// lacking eq_u is not, and one lacking next_u_c on its second letter is not.
TEST(DerivedFreeCheckerAssignments, TheStatementsAreAssumptions) {
  std::vector<EnabledAssertion> assumptions{
      {*FreeCheckerRandAssignment("u", Equality), BoolTrue()},
      {*FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue),
       BoolTrue()}};
  EXPECT_TRUE(WordIsFeasible(Word{A({"eq_u", "next_u_c"}), A({"next_u_c"})},
                             assumptions));
  EXPECT_FALSE(
      WordIsFeasible(Word{A({"next_u_c"}), A({"next_u_c"})}, assumptions));
  EXPECT_FALSE(
      WordIsFeasible(Word{A({"eq_u", "next_u_c"}), A({"x"})}, assumptions));
}

}  // namespace
