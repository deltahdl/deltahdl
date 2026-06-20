#include "elaborator/annex_f_vacuity.h"

#include <algorithm>
#include <cstddef>
#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {
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

// §F.5: the first i letters of w; the empty word when i = 0.
Word FirstLetters(const Word& word, std::size_t i) {
  const std::size_t count = std::min(i, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// The least index at which a letter of the word satisfies b, or word.size() if
// no letter does. With b never satisfied this equals |w|, which is exactly the
// "for every 0 <= i < |w|, w^i |/= b" condition the abort/disable rules use.
std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b) {
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], b)) {
      return i;
    }
  }
  return word.size();
}

// A structural bound on how far a sequence can reach into a word, mirroring the
// bound §F.5.3.1 uses: enough tail letters past an explicit prefix that
// extending a constant T^omega / _|_^omega tail cannot change a tight match.
std::size_t SequenceReach(const SequenceExpr& seq) {
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
    case SequenceExpr::Kind::kLocalVarSampling:
    case SequenceExpr::Kind::kNullRepeat:
      return 1;
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
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

// A structural bound on how far a property can reach into a word; once a word's
// suffix lies entirely inside a constant tail this many letters past the
// explicit prefix, extending the tail cannot change the verdict.
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

// A finite materialization of a prefix followed by a constant tail (T^omega or
// _|_^omega), padded `reach` letters past the prefix plus a margin -- enough
// for the verdict to have stabilized for the finite properties this model
// handles, matching §F.5.3.1's PrefixWithTail.
Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach) {
  Word out = prefix;
  const std::size_t pad = reach + 2;
  for (std::size_t i = 0; i < pad; ++i) {
    out.push_back(tail);
  }
  return out;
}

bool NonVacuous(const Word& word, const PropertyExpr& property);

// §F.5.3.3: the abort/disable family shares one shape. w |=^non OP(b) P iff
// w |=^non P and one of: (1) for every 0 <= i < |w|, w^i |/= b; or (2) there is
// a prefix x of w with no letter satisfying b such that x _|_^omega |/= P or
// x T^omega |/= P. accept_on (b) P and disable iff (b) P both use this rule.
bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const PropertyExpr& operand) {
  if (!NonVacuous(word, operand)) {
    return false;
  }
  const std::size_t first_b = FirstSatisfyingIndex(word, boolean);
  // (1) No letter of w satisfies b.
  if (first_b == word.size()) {
    return true;
  }
  // (2) Some b-free prefix x leaves P unmet under one of the constant tails.
  // The prefixes with no b-letter are exactly those of length 0..first_b.
  const std::size_t reach = PropertyReach(operand);
  for (std::size_t len = 0; len <= first_b; ++len) {
    const Word prefix = FirstLetters(word, len);
    const Word bottom = PrefixWithTail(prefix, LetterBottom(), reach);
    const Word top = PrefixWithTail(prefix, LetterTop(), reach);
    if (!NeutrallySatisfies(bottom, operand) ||
        !NeutrallySatisfies(top, operand)) {
      return true;
    }
  }
  return false;
}

bool NonVacuous(const Word& word, const PropertyExpr& property) {
  switch (property.kind) {
    case PropertyExpr::Kind::kStrong:
    case PropertyExpr::Kind::kWeak:
      // §F.5.3.3 base: w |=^non strong(R) and w |=^non weak(R) hold for every
      // w.
      return true;
    case PropertyExpr::Kind::kParen:
      // §F.5.3.3: w |=^non ( P ) iff w |=^non P.
      return property.lhs && NonVacuous(word, *property.lhs);
    case PropertyExpr::Kind::kNot:
      // §F.5.3.3: w |=^non not P iff w-bar |=^non P.
      return property.lhs && NonVacuous(ComplementWord(word), *property.lhs);
    case PropertyExpr::Kind::kImplication: {
      // §F.5.3.3: w |=^non R |-> P iff there exists i >= 0 such that
      // w^{0,i} |= R (tight satisfaction of the sequence trigger) and
      // w^{i.} |=^non P. Unlike §F.5.3.1's neutral implication, the trigger is
      // measured on w itself, not on w-bar.
      if (!property.sequence || !property.lhs) {
        return false;
      }
      for (std::size_t i = 0; i < word.size(); ++i) {
        if (TightlySatisfies(PrefixInclusive(word, i), *property.sequence) &&
            NonVacuous(Suffix(word, i), *property.lhs)) {
          return true;
        }
      }
      return false;
    }
    case PropertyExpr::Kind::kOr:
      // §F.5.3.3: w |=^non ( P1 or P2 ) iff w |=^non P1 or w |=^non P2.
      return (property.lhs && NonVacuous(word, *property.lhs)) ||
             (property.rhs && NonVacuous(word, *property.rhs));
    case PropertyExpr::Kind::kAnd:
      // §F.5.3.3: w |=^non ( P1 and P2 ) iff w |=^non P1 or w |=^non P2. A
      // conjunction is nonvacuous when either conjunct is, not both.
      return (property.lhs && NonVacuous(word, *property.lhs)) ||
             (property.rhs && NonVacuous(word, *property.rhs));
    case PropertyExpr::Kind::kNexttime:
      // §F.5.3.3: w |=^non ( nexttime P ) iff |w| > 0 and w^{1.} |=^non P.
      return !word.empty() && property.lhs &&
             NonVacuous(Suffix(word, 1), *property.lhs);
    case PropertyExpr::Kind::kUntil: {
      // §F.5.3.3: w |=^non ( P1 until P2 ) iff there exists 0 <= i < |w| with
      // ( w^{i.} |=^non P1 or w^{i.} |=^non P2 ) and, for all 0 <= j < i,
      // w^{j.} |= ( P1 and not P2 ) under neutral satisfaction.
      if (!property.lhs || !property.rhs) {
        return false;
      }
      const std::shared_ptr<const PropertyExpr> guard =
          PropAnd(property.lhs, PropNot(property.rhs));
      for (std::size_t i = 0; i < word.size(); ++i) {
        const Word suffix_i = Suffix(word, i);
        if (!NonVacuous(suffix_i, *property.lhs) &&
            !NonVacuous(suffix_i, *property.rhs)) {
          continue;
        }
        bool prefix_holds = true;
        for (std::size_t j = 0; j < i; ++j) {
          if (!NeutrallySatisfies(Suffix(word, j), *guard)) {
            prefix_holds = false;
            break;
          }
        }
        if (prefix_holds) {
          return true;
        }
      }
      return false;
    }
    case PropertyExpr::Kind::kAcceptOn:
      // §F.5.3.3: w |=^non ( accept_on (b) P ) shares the abort/disable shape.
      return property.boolean && property.lhs &&
             NonVacuousAbortShape(word, *property.boolean, *property.lhs);
  }
  return false;
}

}  // namespace

bool NonVacuouslyEvaluates(const Word& word, const PropertyExpr& property) {
  return NonVacuous(word, property);
}

bool NonVacuouslyEvaluatesTopLevel(const Word& word,
                                   const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      // §F.5.3.3 applies to the property directly.
      return top.property && NonVacuous(word, *top.property);
    case TopLevelProperty::Kind::kDisableIff:
      // §F.5.3.3: w |=^non disable iff (b) P uses the same shape as accept_on.
      return top.disable_condition && top.property &&
             NonVacuousAbortShape(word, *top.disable_condition, *top.property);
    case TopLevelProperty::Kind::kParen:
      // A parenthesized top-level property is transparent, as for ( P ).
      return top.inner && NonVacuouslyEvaluatesTopLevel(word, *top.inner);
  }
  return false;
}

bool SatisfiesNonVacuously(const Word& word, const PropertyExpr& property) {
  // §F.5.3.3: w satisfies P nonvacuously iff w |= P and w |=^non P.
  return NeutrallySatisfies(word, property) &&
         NonVacuouslyEvaluates(word, property);
}

bool SatisfiesTopLevelNonVacuously(const Word& word,
                                   const TopLevelProperty& top) {
  // §F.5.3.3 at the top level: neutral satisfaction together with non-vacuity.
  return NeutrallySatisfiesTopLevel(word, top) &&
         NonVacuouslyEvaluatesTopLevel(word, top);
}

}  // namespace delta
