#include "elaborator/annex_f_finite_word_satisfaction.h"

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool WeaklySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion) {
  return NeutrallySatisfiesAssertionWithTail(word, LetterTop(), enabling,
                                             assertion);
}

bool StronglySatisfiesByFiniteWord(const Word& word,
                                   const BooleanExpr& enabling,
                                   const AssertionStatement& assertion) {
  return NeutrallySatisfiesAssertionWithTail(word, LetterBottom(), enabling,
                                             assertion);
}

FiniteWordVerdict CheckFiniteWord(const Word& word, const BooleanExpr& enabling,
                                  const AssertionStatement& assertion) {
  if (!WeaklySatisfiesByFiniteWord(word, enabling, assertion)) {
    return FiniteWordVerdict::kFails;
  }
  if (StronglySatisfiesByFiniteWord(word, enabling, assertion)) {
    return FiniteWordVerdict::kHoldsStrongly;
  }
  if (NeutrallySatisfiesAssertion(word, enabling, assertion)) {
    return FiniteWordVerdict::kHolds;
  }
  return FiniteWordVerdict::kPending;
}

bool FiniteWordVerdictCondition(FiniteWordVerdict verdict, const Word& word,
                                const BooleanExpr& enabling,
                                const AssertionStatement& assertion) {
  switch (verdict) {
    case FiniteWordVerdict::kHoldsStrongly:
      return StronglySatisfiesByFiniteWord(word, enabling, assertion);
    case FiniteWordVerdict::kFails:
      return !WeaklySatisfiesByFiniteWord(word, enabling, assertion);
    case FiniteWordVerdict::kHolds:
      return NeutrallySatisfiesAssertion(word, enabling, assertion) &&
             !StronglySatisfiesByFiniteWord(word, enabling, assertion);
    case FiniteWordVerdict::kPending:
      return WeaklySatisfiesByFiniteWord(word, enabling, assertion) &&
             !NeutrallySatisfiesAssertion(word, enabling, assertion);
  }
  return false;
}

const char* FiniteWordVerdictLabel(FiniteWordVerdict verdict) {
  switch (verdict) {
    case FiniteWordVerdict::kHoldsStrongly:
      return "Holds strongly";
    case FiniteWordVerdict::kFails:
      return "Fails";
    case FiniteWordVerdict::kHolds:
      return "Holds (but does not hold strongly)";
    case FiniteWordVerdict::kPending:
      return "Pending";
  }
  return "";
}

}  // namespace delta
