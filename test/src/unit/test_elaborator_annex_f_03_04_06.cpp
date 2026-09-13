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
// === (c ? e : u)), each evaluated under the enabling condition b of the
// conditional statements the assignment is in the scope of. The Boolean each
// compares is outside the §F.3.2 Boolean model, so the caller supplies it and
// the cases stand it in by an atom. The cases check that each factory builds
// the statement its identity names -- the role, the activation, the @1 clock
// form and the weak reading of the bare Boolean -- that the caller's Boolean
// is asked about the name and the clock given, that the enabling condition
// given is the one the assumption is paired with, and that, under §F.5.3.1,
// the rand form constrains the first letter alone where the always_ff form
// constrains every letter, and an enabling condition absent at an activation
// lets that letter go.

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

// The two assignments as written in the scope of no conditional statement,
// whose enabling condition is then the constant 1.
EnabledAssertion Rand() {
  return FreeCheckerRandAssignment("u", Equality, BoolTrue());
}
EnabledAssertion AlwaysFf() {
  return FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue,
                                       BoolTrue());
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
  const AssertionStatement kStatement = Rand().statement;
  EXPECT_EQ(kStatement.activation, AssertionStatement::Activation::kInitial);
  EXPECT_EQ(kStatement.role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(kStatement, "eq_u");
}

// always_ff @c u <= e is an always assume property statement whose body is
// @1 over the weak reading of $future_gclk(u) === (c ? e : u).
TEST(DerivedFreeCheckerAssignments, AlwaysFfAssignmentIsAnAlwaysAssume) {
  const AssertionStatement kStatement = AlwaysFf().statement;
  EXPECT_EQ(kStatement.activation, AssertionStatement::Activation::kAlways);
  EXPECT_EQ(kStatement.role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(kStatement, "next_u_c");
}

// The enabling condition given is the one the assumption is paired with: the
// constant 1 for an assignment in the scope of no conditional statement, and
// the resulting condition b of the conditional statements it is in the scope
// of otherwise, for either form.
TEST(DerivedFreeCheckerAssignments, TheEnablingConditionIsTheOneGiven) {
  auto one = BoolTrue();
  auto b = BoolAtom("b");
  EXPECT_EQ(FreeCheckerRandAssignment("u", Equality, one).enabling, one);
  EXPECT_EQ(FreeCheckerRandAssignment("u", Equality, b).enabling, b);
  EXPECT_EQ(FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue, one)
                .enabling,
            one);
  EXPECT_EQ(
      FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue, b).enabling,
      b);
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
  FreeCheckerRandAssignment("v", kRecordingEquality, BoolTrue());
  ASSERT_EQ(names.size(), 1U);
  EXPECT_EQ(names[0], "v");
  EXPECT_TRUE(clocks.empty());
  auto c = BoolAtom("c");
  FreeCheckerAlwaysFfAssignment("w", c, kRecordingNextValue, BoolTrue());
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
  const AssertionStatement kStatement = Rand().statement;
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"eq_u"}), A({"x"})},
                                          *BoolTrue(), kStatement));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"eq_u"})}, *BoolTrue(), kStatement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"eq_u"})},
                                           *BoolTrue(), kStatement));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), kStatement));
}

// Under §F.5.3.1, the always_ff form is judged at every letter: it holds
// where next_u_c is on each letter and fails where any letter lacks it, so a
// word the rand form of the same atom accepts is one it rejects.
TEST(DerivedFreeCheckerAssignments, TheAlwaysFfFormConstrainsEveryLetter) {
  const AssertionStatement kStatement = AlwaysFf().statement;
  EXPECT_TRUE(NeutrallySatisfiesAssertion(
      Word{A({"next_u_c"}), A({"next_u_c"})}, *BoolTrue(), kStatement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"next_u_c"}), A({"x"})},
                                           *BoolTrue(), kStatement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"next_u_c"})},
                                           *BoolTrue(), kStatement));
  const AssertionStatement kRandOfSameAtom =
      FreeCheckerRandAssignment(
          "u",
          [](const std::string& u) { return BoolAtom("next_" + u + "_c"); },
          BoolTrue())
          .statement;
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"next_u_c"}), A({"x"})},
                                          *BoolTrue(), kRandOfSameAtom));
}

// Under §F.5.3.1, the enabling condition gates each activation: with the
// assignment in the scope of a conditional whose resulting condition is b,
// the always_ff form lets a letter without the comparison go where b is
// absent there and still rejects it where b is present, which the constant 1
// would reject either way, and the rand form lets a first letter without the
// equality go where b is absent there and rejects it where b is present.
TEST(DerivedFreeCheckerAssignments, TheEnablingConditionGatesEachActivation) {
  const EnabledAssertion kAlwaysFf = FreeCheckerAlwaysFfAssignment(
      "u", BoolAtom("c"), NextValue, BoolAtom("b"));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"b", "next_u_c"}), A({"x"})},
                                          *kAlwaysFf.enabling,
                                          kAlwaysFf.statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"b", "next_u_c"}), A({"b"})},
                                           *kAlwaysFf.enabling,
                                           kAlwaysFf.statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"b", "next_u_c"}), A({"x"})},
                                           *BoolTrue(), kAlwaysFf.statement));
  const EnabledAssertion kRand =
      FreeCheckerRandAssignment("u", Equality, BoolAtom("b"));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"})}, *kRand.enabling,
                                          kRand.statement));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"b"})}, *kRand.enabling,
                                           kRand.statement));
}

// Both statements are assumptions, so under §F.5.3.1 a word is feasible
// under them iff each is satisfied on it: with both in force, a word with
// eq_u on the first letter and next_u_c on every letter is feasible, one
// lacking eq_u is not, and one lacking next_u_c on its second letter is not.
TEST(DerivedFreeCheckerAssignments, TheStatementsAreAssumptions) {
  std::vector<EnabledAssertion> assumptions{Rand(), AlwaysFf()};
  EXPECT_TRUE(WordIsFeasible(Word{A({"eq_u", "next_u_c"}), A({"next_u_c"})},
                             assumptions));
  EXPECT_FALSE(
      WordIsFeasible(Word{A({"next_u_c"}), A({"next_u_c"})}, assumptions));
  EXPECT_FALSE(
      WordIsFeasible(Word{A({"eq_u", "next_u_c"}), A({"x"})}, assumptions));
}

}  // namespace
