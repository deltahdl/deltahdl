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

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

using Activation = AssertionStatement::Activation;
using Role = AssertionStatement::Role;

std::shared_ptr<const SequenceExpr> Sampling() {
  return SeqConcat(Bs("a"), SeqLocalVarSampling("v"));
}

std::shared_ptr<const LvAssertionStatement> InitialSampling() {
  return LvAssertionWithClock(
      Activation::kInitial, Role::kAssert, BoolAtom("clk"),
      LvClockedTopLocalVarDecl("int", "v",
                               LvClockedTopProperty(ClkStrong(Sampling()))));
}

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

TEST(FiniteWordSatisfactionLocals,
     TheVerdictsWithoutLocalsAgreeWithTheLocalFreeSemantics) {
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
