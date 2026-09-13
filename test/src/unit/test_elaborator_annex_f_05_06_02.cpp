#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_finite_word_satisfaction_local_variables.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.5.6.2 has weak and strong satisfaction by finite words with local
// variables be the definition of §F.5.3.2 with the understanding that the
// underlying properties can have local variables. The cases check the two
// completions on a statement whose body declares and samples a local, that
// the tail carries activation points as in §F.5.3.2, that on bodies without
// local variables the relations and the verdict are §F.5.3.2's, and that the
// four conditions partition the pairs of the family with the verdict the one
// whose condition holds.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

using Activation = AssertionStatement::Activation;
using Role = AssertionStatement::Role;

// a ##1 (1, v = e): a sequence that samples a local at the letter after a.
std::shared_ptr<const SequenceExpr> Sampling() {
  return SeqConcat(Bs("a"), SeqLocalVarSampling("v"));
}

// initial @( clk ) assert property ( int v ; strong( a ##1 (1, v = e) ) ).
std::shared_ptr<const LvAssertionStatement> InitialSampling() {
  return LvAssertionWithClock(
      Activation::kInitial, Role::kAssert, BoolAtom("clk"),
      LvClockedTopLocalVarDecl("int", "v",
                               LvClockedTopProperty(ClkStrong(Sampling()))));
}

// §F.5.6.2: the completions decide a statement whose body carries local
// variables as they do one without. The initial statement holds strongly on
// [a,clk][b,clk], where the sampling is met at the second tick; is pending on
// [a,clk], where the top tail supplies that tick and the word does not; fails
// on [x,clk], whose first tick lacks a under either tail; and holds without
// holding strongly on the empty word, which no letter of the top tail
// activates and every letter of the bottom tail activates and fails.
TEST(FiniteWordSatisfactionLocals, TheCompletionsDecideAStatementWithLocals) {
  auto a = InitialSampling();
  const Word kMet{A({"a", "clk"}), A({"b", "clk"})};
  const Word kOpen{A({"a", "clk"})};
  const Word kMissed{A({"x", "clk"})};
  EXPECT_TRUE(StronglySatisfiesByFiniteWordWithLocals(kMet, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWordWithLocals(kMet, *BoolTrue(), *a),
            FiniteWordVerdict::kHoldsStrongly);
  EXPECT_TRUE(WeaklySatisfiesByFiniteWordWithLocals(kOpen, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(kOpen, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWordWithLocals(kOpen, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWordWithLocals(kOpen, *BoolTrue(), *a),
            FiniteWordVerdict::kPending);
  EXPECT_FALSE(WeaklySatisfiesByFiniteWordWithLocals(kMissed, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWordWithLocals(kMissed, *BoolTrue(), *a),
            FiniteWordVerdict::kFails);
  EXPECT_TRUE(WeaklySatisfiesByFiniteWordWithLocals(Word{}, *BoolTrue(), *a));
  EXPECT_TRUE(NeutrallySatisfiesAssertionWithLocals(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(
      StronglySatisfiesByFiniteWordWithLocals(Word{}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWordWithLocals(Word{}, *BoolTrue(), *a),
            FiniteWordVerdict::kHolds);
}

// §F.5.6.2: the completion is an infinite word, so an always form has
// activation points in the tail as in §F.5.3.2. always @( 1 ) assert
// property strong( a ##1 (1, v = e) ) on [a]: the one activation sees a
// suffix the top tail completes with the letter the sampling is met on and
// no letter of that tail activates the statement, so the word satisfies it
// weakly, while it neither neutrally nor strongly satisfies it.
TEST(FiniteWordSatisfactionLocals, TheTailHasActivationPointsOfItsOwn) {
  auto a = LvAssertionWithClock(Activation::kAlways, Role::kAssert, BoolTrue(),
                                LvClockedTopProperty(ClkStrong(Sampling())));
  const Word kWord{A({"a"})};
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(kWord, *BoolTrue(), *a));
  EXPECT_TRUE(WeaklySatisfiesByFiniteWordWithLocals(kWord, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWordWithLocals(kWord, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWordWithLocals(kWord, *BoolTrue(), *a),
            FiniteWordVerdict::kPending);
}

// The words the agreement and partition cases range over.
std::vector<Word> Words() {
  return {Word{},
          Word{A({"a", "clk"})},
          Word{A({"a", "clk"}), A({"b", "clk"})},
          Word{A({"x", "clk"})},
          Word{A({"a", "clk"}), A({"x"}), A({"b", "clk"})},
          Word{A({"x", "clk"}), A({"a", "clk"}), A({"b", "clk"})},
          Word{LetterTop()},
          Word{A({"a", "clk"}), LetterBottom()}};
}

// A statement without local variables in the §F.5.6.1 model beside the same
// statement in the §F.5.3.1 model: @( clk ) strong( a ##1 b ) in the U shape
// and in the @( c ) T shape, under each activation and role.
struct Paired {
  std::shared_ptr<const LvAssertionStatement> lv;
  std::shared_ptr<const AssertionStatement> plain;
};
std::vector<Paired> PairsWithoutLocals() {
  const auto kAThenB = SeqConcat(Bs("a"), Bs("b"));
  auto q = ClkClock(BoolAtom("clk"), ClkStrong(kAThenB));
  const std::vector<std::pair<Activation, Role>> kShapes{
      {Activation::kAlways, Role::kAssert},
      {Activation::kAlways, Role::kCover},
      {Activation::kInitial, Role::kAssert},
      {Activation::kInitial, Role::kCover}};
  std::vector<Paired> out;
  for (const auto& [activation, role] : kShapes) {
    out.push_back(
        {LvAssertionWithClockedTop(activation, role, LvClockedTopProperty(q)),
         AssertionWithClockedTop(activation, role, ClockedTopProperty(q))});
    out.push_back(
        {LvAssertionWithClock(activation, role, BoolAtom("clk"),
                              LvClockedTopProperty(ClkStrong(kAThenB))),
         AssertionWithClock(activation, role, BoolAtom("clk"),
                            TopProperty(PropStrong(kAThenB)))});
  }
  return out;
}

// §F.5.6.2: on a body without local variables the two relations and the
// verdict are §F.5.3.2's, for both shapes of body, both activations and the
// assert and cover roles, with every verdict occurring.
TEST(FiniteWordSatisfactionLocals, TheVerdictsAgreeWithF532WithoutLocals) {
  std::set<FiniteWordVerdict> seen;
  for (const Paired& pair : PairsWithoutLocals()) {
    for (const Word& w : Words()) {
      EXPECT_EQ(WeaklySatisfiesByFiniteWordWithLocals(w, *BoolTrue(), *pair.lv),
                WeaklySatisfiesByFiniteWord(w, *BoolTrue(), *pair.plain));
      EXPECT_EQ(
          StronglySatisfiesByFiniteWordWithLocals(w, *BoolTrue(), *pair.lv),
          StronglySatisfiesByFiniteWord(w, *BoolTrue(), *pair.plain));
      const FiniteWordVerdict kVerdict =
          CheckFiniteWordWithLocals(w, *BoolTrue(), *pair.lv);
      EXPECT_EQ(kVerdict, CheckFiniteWord(w, *BoolTrue(), *pair.plain));
      seen.insert(kVerdict);
    }
  }
  EXPECT_EQ(seen.size(), 4U);
}

// The statements the partition case ranges over: bodies that declare and
// sample a local, negate such a sequence or sample under a weak, under both
// activations and both roles, in the U shape.
std::vector<std::shared_ptr<const LvAssertionStatement>> Statements() {
  auto clocked = [](std::shared_ptr<const ClockedProperty> q) {
    return ClkClock(BoolAtom("clk"), std::move(q));
  };
  const std::vector<std::shared_ptr<const LvClockedTopLevelProperty>> kBodies{
      LvClockedTopLocalVarDecl(
          "int", "v", LvClockedTopProperty(clocked(ClkStrong(Sampling())))),
      LvClockedTopProperty(clocked(ClkNot(ClkStrong(Sampling())))),
      LvClockedTopProperty(clocked(ClkWeak(Sampling()))),
      LvClockedTopDisableIff(BoolAtom("x"), clocked(ClkStrong(Sampling()))),
  };
  std::vector<std::shared_ptr<const LvAssertionStatement>> out;
  for (const auto& body : kBodies) {
    for (Activation activation : {Activation::kInitial, Activation::kAlways}) {
      for (Role role : {Role::kAssert, Role::kCover}) {
        out.push_back(LvAssertionWithClockedTop(activation, role, body));
      }
    }
  }
  return out;
}

// The verdicts whose condition holds of a word and a statement.
std::vector<FiniteWordVerdict> VerdictsHolding(const Word& word,
                                               const LvAssertionStatement& a) {
  const std::vector<FiniteWordVerdict> kVerdicts{
      FiniteWordVerdict::kHoldsStrongly, FiniteWordVerdict::kFails,
      FiniteWordVerdict::kHolds, FiniteWordVerdict::kPending};
  std::vector<FiniteWordVerdict> out;
  for (FiniteWordVerdict verdict : kVerdicts) {
    if (FiniteWordVerdictConditionWithLocals(verdict, word, *BoolTrue(), a)) {
      out.push_back(verdict);
    }
  }
  return out;
}

// §F.5.6.2: the four conditions of §F.5.3.2 partition the pairs of a word
// and a statement with local variables, and the verdict returned is the one
// whose condition holds; every verdict occurs on the family.
TEST(FiniteWordSatisfactionLocals, TheVerdictIsTheOneConditionThatHolds) {
  std::set<FiniteWordVerdict> seen;
  for (const auto& a : Statements()) {
    for (const Word& w : Words()) {
      const std::vector<FiniteWordVerdict> kHolding = VerdictsHolding(w, *a);
      ASSERT_EQ(kHolding.size(), 1U);
      EXPECT_EQ(kHolding[0], CheckFiniteWordWithLocals(w, *BoolTrue(), *a));
      seen.insert(kHolding[0]);
    }
  }
  EXPECT_EQ(seen.size(), 4U);
}

}  // namespace
