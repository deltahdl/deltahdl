#pragma once

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.3.2 defines weak and strong satisfaction of an assertion statement A by a
// finite (possibly empty) word w over Sigma, written w |=^- A and w |=^+ A. Both
// are layered directly on §F.5.3.1's neutral satisfaction of A by an infinite
// word (NeutrallySatisfiesAssertion, a satisfied dependency): the finite word is
// completed with a constant tail and that relation decides the result.
//   - w |=^- A iff (w followed by the infinite top tail T^omega) neutrally
//     satisfies A.
//   - w |=^+ A iff (w followed by the infinite bottom tail _|_^omega) neutrally
//     satisfies A.
// The enabling condition b is threaded through exactly as in §F.5.3.1, where it
// is 1 for a declarative assertion statement.

// §F.5.3.2: weak satisfaction w |=^- A. The finite word is completed with an
// infinite run of the top letter T before applying neutral satisfaction.
bool WeaklySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion);

// §F.5.3.2: strong satisfaction w |=^+ A. The finite word is completed with an
// infinite run of the bottom letter _|_ before applying neutral satisfaction.
bool StronglySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                   const AssertionStatement& assertion);

// §F.5.3.2: the four verdicts a tool checking satisfaction of A by the finite
// word w should return.
enum class FiniteWordVerdict {
  kHoldsStrongly,  // "Holds strongly": w |=^+ A.
  kFails,          // "Fails": not (w |=^- A).
  kHolds,          // "Holds (but does not hold strongly)": w |= A and not w |=^+ A.
  kPending,        // "Pending": w |=^- A and not w |= A.
};

// §F.5.3.2: classify the finite word w against the assertion A into the verdict a
// tool should return. Strong satisfaction implies neutral satisfaction, which
// implies weak satisfaction, so testing weak, then strong, then neutral selects
// exactly one of the four mutually exclusive conditions the standard lists.
FiniteWordVerdict CheckFiniteWord(const Word& word, const BooleanExpr& enabling,
                                  const AssertionStatement& assertion);

// §F.5.3.2: the label a tool reports for each verdict.
const char* FiniteWordVerdictLabel(FiniteWordVerdict verdict);

}  // namespace delta
