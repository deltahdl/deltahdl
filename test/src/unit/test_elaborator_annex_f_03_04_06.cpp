#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const BooleanExpr> Equality(const std::string& u) {
  return BoolAtom("eq_" + u);
}
std::shared_ptr<const BooleanExpr> NextValue(
    const std::string& u, const std::shared_ptr<const BooleanExpr>& c) {
  return BoolAtom("next_" + u + "_" + c->atom);
}

EnabledAssertion Rand() {
  return FreeCheckerRandAssignment("u", Equality, BoolTrue());
}
EnabledAssertion AlwaysFf() {
  return FreeCheckerAlwaysFfAssignment("u", BoolAtom("c"), NextValue,
                                       BoolTrue());
}

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

TEST(DerivedFreeCheckerAssignments, RandAssignmentIsAnInitialAssume) {
  const AssertionStatement kStatement = Rand().statement;
  EXPECT_EQ(kStatement.activation, AssertionStatement::Activation::kInitial);
  EXPECT_EQ(kStatement.role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(kStatement, "eq_u");
}

TEST(DerivedFreeCheckerAssignments, AlwaysFfAssignmentIsAnAlwaysAssume) {
  const AssertionStatement kStatement = AlwaysFf().statement;
  EXPECT_EQ(kStatement.activation, AssertionStatement::Activation::kAlways);
  EXPECT_EQ(kStatement.role, AssertionStatement::Role::kAssume);
  ExpectBodyIsWeakAtGlobalClock(kStatement, "next_u_c");
}

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
