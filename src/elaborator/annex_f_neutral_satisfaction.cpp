#include "elaborator/annex_f_neutral_satisfaction.h"

#include <algorithm>
#include <cstddef>
#include <memory>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::shared_ptr<const PropertyExpr> PropStrong(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kStrong;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const PropertyExpr> PropWeak(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kWeak;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const PropertyExpr> PropParen(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kParen;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropNot(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kNot;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const PropertyExpr> consequent) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kImplication;
  p->sequence = std::move(antecedent);
  p->lhs = std::move(consequent);
  return p;
}

std::shared_ptr<const PropertyExpr> PropOr(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kOr;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropAnd(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kAnd;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropNexttime(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kNexttime;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropUntil(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kUntil;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kAcceptOn;
  p->boolean = std::move(b);
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const TopLevelProperty> TopProperty(
    std::shared_ptr<const PropertyExpr> p) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kProperty;
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const TopLevelProperty> TopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kDisableIff;
  t->disable_condition = std::move(b);
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const TopLevelProperty> TopParen(
    std::shared_ptr<const TopLevelProperty> inner) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kParen;
  t->inner = std::move(inner);
  return t;
}

namespace {

// §F.5 (page 1246): w-bar interchanges T and _|_; a letter in 2^P is unchanged.
Letter ComplementLetter(const Letter& letter) {
  switch (letter.kind) {
    case Letter::Kind::kTop:
      return LetterBottom();
    case Letter::Kind::kBottom:
      return LetterTop();
    case Letter::Kind::kAtomSet:
      return letter;
  }
  return letter;
}

// §F.5: w-bar, the letterwise complement of the whole word.
Word ComplementWord(const Word& word) {
  Word out;
  out.reserve(word.size());
  for (const Letter& letter : word) {
    out.push_back(ComplementLetter(letter));
  }
  return out;
}

// §F.5: w^{i.}, the word with its first i letters deleted (empty once i reaches
// the length of w).
Word Suffix(const Word& word, std::size_t i) {
  if (i >= word.size()) {
    return Word{};
  }
  return Word(word.begin() + static_cast<std::ptrdiff_t>(i), word.end());
}

// §F.5: w^{0,k}, the finite prefix w^0 w^1 ... w^k (the first k+1 letters).
Word PrefixInclusive(const Word& word, std::size_t k) {
  const std::size_t count = std::min(k + 1, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// §F.5: the first i letters w^{0,i-1}; the empty word when i = 0 (the standard
// notes w^{0,-1} denotes the empty word).
Word FirstLetters(const Word& word, std::size_t i) {
  const std::size_t count = std::min(i, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// A structural bound on how far a sequence can reach into a word: the maximum
// number of letters a tight match can consume. Unbounded repeats are bounded by
// a single iteration, which is the shortest witness on a constant T^omega tail.
std::size_t SequenceReach(const SequenceExpr& seq) {
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
    case SequenceExpr::Kind::kLocalVarSampling:
      return 1;
    case SequenceExpr::Kind::kNullRepeat:
      return 1;
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      return seq.lhs ? SequenceReach(*seq.lhs) : 1;
    case SequenceExpr::Kind::kLocalVarDecl:
      return seq.lhs ? SequenceReach(*seq.lhs) : 1;
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      return (seq.lhs ? SequenceReach(*seq.lhs) : 0) +
             (seq.rhs ? SequenceReach(*seq.rhs) : 0);
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      return std::max(seq.lhs ? SequenceReach(*seq.lhs) : 0,
                      seq.rhs ? SequenceReach(*seq.rhs) : 0);
    case SequenceExpr::Kind::kClock:
      return (seq.lhs ? SequenceReach(*seq.lhs) : 1) + 1;
  }
  return 1;
}

// A structural bound on how far a property can reach into a word. Once a word's
// suffix lies entirely inside a constant T^omega or _|_^omega tail this many
// letters past the explicit prefix, extending the tail cannot change the
// verdict, so it sets how many tail letters need to be materialized.
std::size_t PropertyReach(const PropertyExpr& property) {
  switch (property.kind) {
    case PropertyExpr::Kind::kStrong:
    case PropertyExpr::Kind::kWeak:
      return property.sequence ? SequenceReach(*property.sequence) : 1;
    case PropertyExpr::Kind::kParen:
    case PropertyExpr::Kind::kNot:
      return property.lhs ? PropertyReach(*property.lhs) : 1;
    case PropertyExpr::Kind::kImplication:
      return (property.sequence ? SequenceReach(*property.sequence) : 0) +
             (property.lhs ? PropertyReach(*property.lhs) : 0);
    case PropertyExpr::Kind::kOr:
    case PropertyExpr::Kind::kAnd:
      return std::max(property.lhs ? PropertyReach(*property.lhs) : 0,
                      property.rhs ? PropertyReach(*property.rhs) : 0);
    case PropertyExpr::Kind::kUntil:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) +
             (property.rhs ? PropertyReach(*property.rhs) : 0) + 1;
    case PropertyExpr::Kind::kNexttime:
    case PropertyExpr::Kind::kAcceptOn:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) + 1;
  }
  return 1;
}

// A finite materialization of w^{0,i-1} followed by a constant tail (T^omega or
// _|_^omega). The tail is padded to `reach` letters past the prefix, plus a
// margin; for the finite properties this model evaluates that is enough for the
// verdict to have stabilized, mirroring §F.5.2's bounded witness search.
Word PrefixWithTail(const Word& prefix, const Letter& tail,
                    std::size_t reach) {
  Word out = prefix;
  const std::size_t pad = reach + 2;
  for (std::size_t i = 0; i < pad; ++i) {
    out.push_back(tail);
  }
  return out;
}

// §F.5.3.1: w |= strong(R) iff there exists 0 <= j < |w| with w^{0,j} |= R.
bool StrongHolds(const Word& word, const SequenceExpr& seq) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (TightlySatisfies(PrefixInclusive(word, j), seq)) {
      return true;
    }
  }
  return false;
}

bool Satisfies(const Word& word, const PropertyExpr& property);

// §F.5.3.1: w |= weak(R) iff for every 0 <= j < |w|, w^{0,j} T^omega |=
// strong(R).
bool WeakHolds(const Word& word, const SequenceExpr& seq) {
  const std::size_t reach = SequenceReach(seq);
  for (std::size_t j = 0; j < word.size(); ++j) {
    const Word completed =
        PrefixWithTail(PrefixInclusive(word, j), LetterTop(), reach);
    if (!StrongHolds(completed, seq)) {
      return false;
    }
  }
  return true;
}

bool Satisfies(const Word& word, const PropertyExpr& property) {
  switch (property.kind) {
    case PropertyExpr::Kind::kParen:
      // §F.5.3.1: w |= ( P ) iff w |= P.
      return property.lhs && Satisfies(word, *property.lhs);
    case PropertyExpr::Kind::kNot:
      // §F.5.3.1: w |= not P iff w-bar |= P.
      return property.lhs && Satisfies(ComplementWord(word), *property.lhs);
    case PropertyExpr::Kind::kStrong:
      // §F.5.3.1: w |= strong(R) iff some w^{0,j} tightly satisfies R.
      return property.sequence && StrongHolds(word, *property.sequence);
    case PropertyExpr::Kind::kWeak:
      // §F.5.3.1: w |= weak(R) iff every T^omega-completed prefix satisfies
      // strong(R).
      return property.sequence && WeakHolds(word, *property.sequence);
    case PropertyExpr::Kind::kImplication: {
      // §F.5.3.1: w |= ( R |-> P ) iff for every 0 <= j < |w| with
      // w-bar^{0,j} |= R, w^{j.} |= P.
      if (!property.sequence || !property.lhs) {
        return false;
      }
      const Word complement = ComplementWord(word);
      for (std::size_t j = 0; j < word.size(); ++j) {
        if (TightlySatisfies(PrefixInclusive(complement, j),
                             *property.sequence) &&
            !Satisfies(Suffix(word, j), *property.lhs)) {
          return false;
        }
      }
      return true;
    }
    case PropertyExpr::Kind::kOr:
      // §F.5.3.1: w |= ( P1 or P2 ) iff w |= P1 or w |= P2.
      return (property.lhs && Satisfies(word, *property.lhs)) ||
             (property.rhs && Satisfies(word, *property.rhs));
    case PropertyExpr::Kind::kAnd:
      // §F.5.3.1: w |= ( P1 and P2 ) iff w |= P1 and w |= P2.
      return property.lhs && property.rhs &&
             Satisfies(word, *property.lhs) && Satisfies(word, *property.rhs);
    case PropertyExpr::Kind::kNexttime:
      // §F.5.3.1: w |= ( nexttime P ) iff |w| = 0 or w^{1.} |= P.
      return word.empty() ||
             (property.lhs && Satisfies(Suffix(word, 1), *property.lhs));
    case PropertyExpr::Kind::kUntil: {
      // §F.5.3.1: w |= ( P1 until P2 ) iff some 0 <= j < |w| has w^{j.} |= P2
      // with w^{i.} |= P1 for all 0 <= i < j, or w^{i.} |= P1 for all i.
      if (!property.lhs || !property.rhs) {
        return false;
      }
      for (std::size_t j = 0; j < word.size(); ++j) {
        if (Satisfies(Suffix(word, j), *property.rhs)) {
          bool prefix_holds = true;
          for (std::size_t i = 0; i < j; ++i) {
            if (!Satisfies(Suffix(word, i), *property.lhs)) {
              prefix_holds = false;
              break;
            }
          }
          if (prefix_holds) {
            return true;
          }
        }
      }
      for (std::size_t i = 0; i < word.size(); ++i) {
        if (!Satisfies(Suffix(word, i), *property.lhs)) {
          return false;
        }
      }
      return true;
    }
    case PropertyExpr::Kind::kAcceptOn: {
      // §F.5.3.1: w |= ( accept_on (b) P ) iff w |= P, or for some 0 <= i < |w|
      // with w^i |= b, w^{0,i-1} T^omega |= P.
      if (!property.boolean || !property.lhs) {
        return false;
      }
      if (Satisfies(word, *property.lhs)) {
        return true;
      }
      const std::size_t reach = PropertyReach(*property.lhs);
      for (std::size_t i = 0; i < word.size(); ++i) {
        if (LetterSatisfiesBoolean(word[i], *property.boolean)) {
          const Word completed =
              PrefixWithTail(FirstLetters(word, i), LetterTop(), reach);
          if (Satisfies(completed, *property.lhs)) {
            return true;
          }
        }
      }
      return false;
    }
  }
  return false;
}

// The least index at which a letter of the word satisfies b, or word.size() if
// no letter does.
std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b) {
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], b)) {
      return i;
    }
  }
  return word.size();
}

}  // namespace

bool NeutrallySatisfies(const Word& word, const PropertyExpr& property) {
  return Satisfies(word, property);
}

bool NeutrallySatisfiesTopLevel(const Word& word,
                                const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      // §F.5.3.1: for T = P, w |= T iff w |= P.
      return top.property && Satisfies(word, *top.property);
    case TopLevelProperty::Kind::kDisableIff: {
      // §F.5.3.1: for T = disable iff (b) P, w |= T iff either w |= P and no
      // letter of w satisfies b, or some letter satisfies b and
      // w^{0,i-1} _|_^omega |= P for i the least index with w^i |= b.
      if (!top.disable_condition || !top.property) {
        return false;
      }
      const std::size_t i = FirstSatisfyingIndex(word, *top.disable_condition);
      if (i == word.size()) {
        return Satisfies(word, *top.property);
      }
      const std::size_t reach = PropertyReach(*top.property);
      const Word completed =
          PrefixWithTail(FirstLetters(word, i), LetterBottom(), reach);
      return Satisfies(completed, *top.property);
    }
    case TopLevelProperty::Kind::kParen:
      // §F.5.3.1: w |= ( T ) iff w |= T.
      return top.inner && NeutrallySatisfiesTopLevel(word, *top.inner);
  }
  return false;
}

bool DisablesTopLevel(const Word& word, const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      // §F.5.3.1: for T = P, w |=^d T never holds.
      return false;
    case TopLevelProperty::Kind::kDisableIff: {
      // §F.5.3.1: for T = disable iff (b) P, w |=^d T iff some letter of w
      // satisfies b and both w^{0,i-1} T^omega |= P and w^{0,i-1} _|_^omega
      // |/= P for i the least index with w^i |= b.
      if (!top.disable_condition || !top.property) {
        return false;
      }
      const std::size_t i = FirstSatisfyingIndex(word, *top.disable_condition);
      if (i == word.size()) {
        return false;
      }
      const std::size_t reach = PropertyReach(*top.property);
      const Word prefix = FirstLetters(word, i);
      const Word top_completed = PrefixWithTail(prefix, LetterTop(), reach);
      const Word bottom_completed =
          PrefixWithTail(prefix, LetterBottom(), reach);
      return Satisfies(top_completed, *top.property) &&
             !Satisfies(bottom_completed, *top.property);
    }
    case TopLevelProperty::Kind::kParen:
      // §F.5.3.1: w |=^d ( T ) iff w |=^d T.
      return top.inner && DisablesTopLevel(word, *top.inner);
  }
  return false;
}

bool PassesTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to pass on w if w |= T."
  return NeutrallySatisfiesTopLevel(word, top);
}

bool IsDisabledTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to be disabled on w if w |=^d T."
  return DisablesTopLevel(word, top);
}

bool FailsTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to fail on w if T neither passes nor is disabled on
  // w." Pass and disabled are mutually exclusive, so failure is their joint
  // negation.
  return !PassesTopLevel(word, top) && !IsDisabledTopLevel(word, top);
}

}  // namespace delta
