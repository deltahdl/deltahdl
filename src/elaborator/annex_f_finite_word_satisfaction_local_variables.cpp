#include "elaborator/annex_f_finite_word_satisfaction_local_variables.h"

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool WeaklySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  return NeutrallySatisfiesAssertionWithLocalsWithTail(word, LetterTop(),
                                                       enabling, assertion);
}

bool StronglySatisfiesByFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  return NeutrallySatisfiesAssertionWithLocalsWithTail(word, LetterBottom(),
                                                       enabling, assertion);
}

FiniteWordVerdict CheckFiniteWordWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  if (!WeaklySatisfiesByFiniteWordWithLocals(word, enabling, assertion)) {
    return FiniteWordVerdict::kFails;
  }
  if (StronglySatisfiesByFiniteWordWithLocals(word, enabling, assertion)) {
    return FiniteWordVerdict::kHoldsStrongly;
  }
  if (NeutrallySatisfiesAssertionWithLocals(word, enabling, assertion)) {
    return FiniteWordVerdict::kHolds;
  }
  return FiniteWordVerdict::kPending;
}

bool FiniteWordVerdictConditionWithLocals(
    FiniteWordVerdict verdict, const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  switch (verdict) {
    case FiniteWordVerdict::kHoldsStrongly:
      return StronglySatisfiesByFiniteWordWithLocals(word, enabling, assertion);
    case FiniteWordVerdict::kFails:
      return !WeaklySatisfiesByFiniteWordWithLocals(word, enabling, assertion);
    case FiniteWordVerdict::kHolds:
      return NeutrallySatisfiesAssertionWithLocals(word, enabling, assertion) &&
             !StronglySatisfiesByFiniteWordWithLocals(word, enabling,
                                                      assertion);
    case FiniteWordVerdict::kPending:
      return WeaklySatisfiesByFiniteWordWithLocals(word, enabling, assertion) &&
             !NeutrallySatisfiesAssertionWithLocals(word, enabling, assertion);
  }
  return false;
}

}  // namespace delta
