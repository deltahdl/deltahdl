#include "elaborator/annex_f_finite_word_satisfaction.h"

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

bool WeaklySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion) {
  // §F.5.3.2: w |=^- A iff w T^omega |= A.
  return NeutrallySatisfiesAssertionWithTail(word, LetterTop(), enabling,
                                             assertion);
}

bool StronglySatisfiesByFiniteWord(const Word& word,
                                   const BooleanExpr& enabling,
                                   const AssertionStatement& assertion) {
  // §F.5.3.2: w |=^+ A iff w _|_^omega |= A.
  return NeutrallySatisfiesAssertionWithTail(word, LetterBottom(), enabling,
                                             assertion);
}

FiniteWordVerdict CheckFiniteWord(const Word& word, const BooleanExpr& enabling,
                                  const AssertionStatement& assertion) {
  // §F.5.3.2: the verdict a tool should return. Because w |=^+ A implies w |=
  // A, which implies w |=^- A, ruling out failure, then strong, then neutral
  // satisfaction picks out exactly one of the four conditions the standard
  // lists.
  if (!WeaklySatisfiesByFiniteWord(word, enabling, assertion)) {
    return FiniteWordVerdict::kFails;  // not (w |=^- A)
  }
  if (StronglySatisfiesByFiniteWord(word, enabling, assertion)) {
    return FiniteWordVerdict::kHoldsStrongly;  // w |=^+ A
  }
  if (NeutrallySatisfiesAssertion(word, enabling, assertion)) {
    return FiniteWordVerdict::kHolds;  // w |= A and not w |=^+ A
  }
  return FiniteWordVerdict::kPending;  // w |=^- A and not w |= A
}

bool FiniteWordVerdictCondition(FiniteWordVerdict verdict, const Word& word,
                                const BooleanExpr& enabling,
                                const AssertionStatement& assertion) {
  // §F.5.3.2: each verdict's condition as the subclause states it.
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
  // §F.5.3.2: the four strings a tool should report.
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
