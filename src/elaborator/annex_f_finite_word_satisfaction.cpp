#include "elaborator/annex_f_finite_word_satisfaction.h"

#include <cstddef>

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {
namespace {

// The finite word w followed by `count` copies of `tail`. The constant tail
// materializes a finite prefix of the infinite completion w T^omega (tail = T)
// or w _|_^omega (tail = _|_) that §F.5.3.2 evaluates against.
Word CompleteWord(const Word& word, const Letter& tail, std::size_t count) {
  Word out = word;
  out.reserve(word.size() + count);
  for (std::size_t i = 0; i < count; ++i) {
    out.push_back(tail);
  }
  return out;
}

// §F.5.3.2: neutral satisfaction of A by the infinite word w tail^omega, the
// completion §F.5.3.1's NeutrallySatisfiesAssertion is asked to decide. The
// tail is constant, so the assertion verdict is eventually independent of how
// many tail letters are present; this materializes a growing finite prefix of
// the tail and returns the verdict once it has held steady across a window. The
// cap keeps the search finite and is exact for the finite assertions this model
// is exercised on, mirroring §F.5.2's bounded witness search and §F.5.3.1's
// PrefixWithTail completion.
bool NeutralOnCompletion(const Word& word, const Letter& tail,
                         const BooleanExpr& enabling,
                         const AssertionStatement& assertion) {
  const std::size_t kCap = word.size() * 4 + 64;
  const std::size_t kWindow = 3;
  bool steady_value = false;
  std::size_t steady_run = 0;
  for (std::size_t count = 1; count <= kCap; ++count) {
    const bool kValue = NeutrallySatisfiesAssertion(
        CompleteWord(word, tail, count), enabling, assertion);
    if (count > 1 && kValue == steady_value) {
      if (++steady_run >= kWindow) {
        return steady_value;
      }
    } else {
      steady_value = kValue;
      steady_run = 1;
    }
  }
  return steady_value;
}

}  // namespace

bool WeaklySatisfiesByFiniteWord(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion) {
  // §F.5.3.2: w |=^- A iff w T^omega |= A.
  return NeutralOnCompletion(word, LetterTop(), enabling, assertion);
}

bool StronglySatisfiesByFiniteWord(const Word& word,
                                   const BooleanExpr& enabling,
                                   const AssertionStatement& assertion) {
  // §F.5.3.2: w |=^+ A iff w _|_^omega |= A.
  return NeutralOnCompletion(word, LetterBottom(), enabling, assertion);
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
