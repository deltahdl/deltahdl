#include "elaborator/annex_f_vacuity.h"

#include <algorithm>
#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {

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

Word ComplementWord(const Word& word) {
  Word out;
  out.reserve(word.size());
  for (const Letter& letter : word) {
    out.push_back(ComplementLetter(letter));
  }
  return out;
}

Word Suffix(const Word& word, std::size_t i) {
  if (i >= word.size()) {
    return Word{};
  }
  return Word(word.begin() + static_cast<std::ptrdiff_t>(i), word.end());
}

Word PrefixInclusive(const Word& word, std::size_t k) {
  const std::size_t kCount = std::min(k + 1, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(kCount));
}

Word FirstLetters(const Word& word, std::size_t i) {
  const std::size_t kCount = std::min(i, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(kCount));
}

std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b) {
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], b)) {
      return i;
    }
  }
  return word.size();
}

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

Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach) {
  Word out = prefix;
  const std::size_t kPad = reach + 2;
  for (std::size_t i = 0; i < kPad; ++i) {
    out.push_back(tail);
  }
  return out;
}

void CollectAtoms(const BooleanExpr& b, std::set<std::string>& out) {
  switch (b.kind) {
    case BooleanExpr::Kind::kTrue:
      return;
    case BooleanExpr::Kind::kAtom:
      out.insert(b.atom);
      return;
    case BooleanExpr::Kind::kNot:
      CollectAtoms(*b.operand_a, out);
      return;
    case BooleanExpr::Kind::kAnd:
      CollectAtoms(*b.operand_a, out);
      CollectAtoms(*b.operand_b, out);
      return;
  }
}

void CollectSequenceAtoms(const SequenceExpr& seq, std::set<std::string>& out,
                          std::size_t& leaf_count) {
  if (seq.kind == SequenceExpr::Kind::kBoolean && seq.boolean != nullptr) {
    CollectAtoms(*seq.boolean, out);
    ++leaf_count;
  }
  if (seq.kind == SequenceExpr::Kind::kClock && seq.boolean != nullptr) {
    CollectAtoms(*seq.boolean, out);
  }
  if (seq.kind == SequenceExpr::Kind::kLocalVarSampling) {
    ++leaf_count;
  }
  if (seq.lhs != nullptr) {
    CollectSequenceAtoms(*seq.lhs, out, leaf_count);
  }
  if (seq.rhs != nullptr) {
    CollectSequenceAtoms(*seq.rhs, out, leaf_count);
  }
}

std::vector<Letter> CandidateAlphabet(const std::set<std::string>& atoms) {
  std::vector<Letter> letters{LetterTop(), LetterBottom()};
  std::vector<std::string> names(atoms.begin(), atoms.end());
  if (names.size() > 6) {
    return letters;
  }
  const std::size_t kSubsetCount = std::size_t{1} << names.size();
  for (std::size_t mask = 0; mask < kSubsetCount; ++mask) {
    std::set<std::string> subset;
    for (std::size_t i = 0; i < names.size(); ++i) {
      if ((mask & (std::size_t{1} << i)) != 0) {
        subset.insert(names[i]);
      }
    }
    letters.push_back(LetterAtoms(std::move(subset)));
  }
  return letters;
}

namespace {

bool NonVacuous(const Word& word, const PropertyExpr& property);

bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const PropertyExpr& operand) {
  return ::delta::NonVacuousAbortShape(
      word, boolean, operand,
      [](const Word& w, const PropertyExpr& p) { return NonVacuous(w, p); },
      [](const Word& w, const PropertyExpr& p) {
        return NeutrallySatisfies(w, p);
      });
}

bool NonVacuousImplication(const Word& word, const PropertyExpr& property) {
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

bool NonVacuousUntil(const Word& word, const PropertyExpr& property) {
  if (!property.lhs || !property.rhs) {
    return false;
  }
  const std::shared_ptr<const PropertyExpr> kGuard =
      PropAnd(property.lhs, PropNot(property.rhs));
  for (std::size_t i = 0; i < word.size(); ++i) {
    const Word kSuffixI = Suffix(word, i);
    if (!NonVacuous(kSuffixI, *property.lhs) &&
        !NonVacuous(kSuffixI, *property.rhs)) {
      continue;
    }
    bool prefix_holds = true;
    for (std::size_t j = 0; j < i; ++j) {
      if (!NeutrallySatisfies(Suffix(word, j), *kGuard)) {
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

bool NonVacuous(const Word& word, const PropertyExpr& property) {
  switch (property.kind) {
    case PropertyExpr::Kind::kStrong:
    case PropertyExpr::Kind::kWeak:
      return true;
    case PropertyExpr::Kind::kParen:
      return property.lhs && NonVacuous(word, *property.lhs);
    case PropertyExpr::Kind::kNot:
      return property.lhs && NonVacuous(ComplementWord(word), *property.lhs);
    case PropertyExpr::Kind::kImplication:
      return NonVacuousImplication(word, property);
    case PropertyExpr::Kind::kOr:
    case PropertyExpr::Kind::kAnd:
      return (property.lhs && NonVacuous(word, *property.lhs)) ||
             (property.rhs && NonVacuous(word, *property.rhs));
    case PropertyExpr::Kind::kNexttime:
      return !word.empty() && property.lhs &&
             NonVacuous(Suffix(word, 1), *property.lhs);
    case PropertyExpr::Kind::kUntil:
      return NonVacuousUntil(word, property);
    case PropertyExpr::Kind::kAcceptOn:
      return property.boolean && property.lhs &&
             NonVacuousAbortShape(word, *property.boolean, *property.lhs);
  }
  return false;
}

bool GuardHolds(const Word& word, const PropertyExpr& p, bool negated) {
  if (negated) {
    return !NeutrallySatisfies(ComplementWord(word), p);
  }
  return NeutrallySatisfies(word, p);
}

bool NonVacuousAfterGuardedPrefix(const Word& word, const PropertyExpr& p,
                                  bool guard_negated, std::size_t first,
                                  std::size_t last) {
  for (std::size_t i = first; i <= last; ++i) {
    if (!NonVacuous(Suffix(word, i), p)) {
      continue;
    }
    bool guarded = true;
    for (std::size_t j = first; j < i; ++j) {
      if (!GuardHolds(Suffix(word, j), p, guard_negated)) {
        guarded = false;
        break;
      }
    }
    if (guarded) {
      return true;
    }
  }
  return false;
}

}  // namespace

bool NonVacuouslyEvaluatesIff(const Word& word, const PropertyExpr& p1,
                              const PropertyExpr& p2) {
  return NonVacuous(word, p1) || NonVacuous(word, p2);
}

bool NonVacuouslyEvaluatesImplies(const Word& word, const PropertyExpr& p1,
                                  const PropertyExpr& p2) {
  return NeutrallySatisfies(word, p1) && NonVacuous(word, p1) &&
         NonVacuous(word, p2);
}

bool NonVacuouslyEvaluatesSUntil(const Word& word, const PropertyExpr& p1,
                                 const PropertyExpr& p2) {
  return NonVacuousUntil(word, *PropUntil(std::make_shared<PropertyExpr>(p1),
                                          std::make_shared<PropertyExpr>(p2)));
}

bool NonVacuouslyEvaluatesAlways(const Word& word, const PropertyExpr& p) {
  return !word.empty() &&
         NonVacuousAfterGuardedPrefix(word, p, false, 0, word.size() - 1);
}

bool NonVacuouslyEvaluatesAlwaysRange(const Word& word, const PropertyExpr& p,
                                      unsigned int m, unsigned int n) {
  return NonVacuousAfterGuardedPrefix(word, p, false, m, n);
}

bool NonVacuouslyEvaluatesSAlwaysRange(const Word& word, const PropertyExpr& p,
                                       unsigned int m, unsigned int n) {
  return NonVacuouslyEvaluatesAlwaysRange(word, p, m, n);
}

bool NonVacuouslyEvaluatesSEventually(const Word& word, const PropertyExpr& p) {
  return !word.empty() &&
         NonVacuousAfterGuardedPrefix(word, p, true, 0, word.size() - 1);
}

bool NonVacuouslyEvaluatesEventuallyRange(const Word& word,
                                          const PropertyExpr& p, unsigned int m,
                                          unsigned int n) {
  return NonVacuousAfterGuardedPrefix(word, p, true, m, n);
}

bool NonVacuouslyEvaluatesSEventuallyRange(const Word& word,
                                           const PropertyExpr& p,
                                           unsigned int m, unsigned int n) {
  return NonVacuouslyEvaluatesEventuallyRange(word, p, m, n);
}

bool NonVacuouslyEvaluatesRejectOn(const Word& word, const BooleanExpr& b,
                                   const PropertyExpr& p) {
  return NonVacuousAbortShape(word, b, p);
}

bool NonVacuouslyEvaluates(const Word& word, const PropertyExpr& property) {
  return NonVacuous(word, property);
}

bool NonVacuouslyEvaluatesTopLevel(const Word& word,
                                   const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      return top.property && NonVacuous(word, *top.property);
    case TopLevelProperty::Kind::kDisableIff:
      return top.disable_condition && top.property &&
             NonVacuousAbortShape(word, *top.disable_condition, *top.property);
    case TopLevelProperty::Kind::kParen:
      return top.inner && NonVacuouslyEvaluatesTopLevel(word, *top.inner);
  }
  return false;
}

bool SatisfiesNonVacuously(const Word& word, const PropertyExpr& property) {
  return NeutrallySatisfies(word, property) &&
         NonVacuouslyEvaluates(word, property);
}

bool SatisfiesTopLevelNonVacuously(const Word& word,
                                   const TopLevelProperty& top) {
  return NeutrallySatisfiesTopLevel(word, top) &&
         NonVacuouslyEvaluatesTopLevel(word, top);
}

}  // namespace delta
