#pragma once

#include <algorithm>
#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

Letter ComplementLetter(const Letter& letter);

Word ComplementWord(const Word& word);

Word Suffix(const Word& word, std::size_t i);

Word PrefixInclusive(const Word& word, std::size_t k);

Word FirstLetters(const Word& word, std::size_t i);

std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b);

std::size_t SequenceReach(const SequenceExpr& seq);

Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach);

void CollectAtoms(const BooleanExpr& b, std::set<std::string>& out);

void CollectSequenceAtoms(const SequenceExpr& seq, std::set<std::string>& out,
                          std::size_t& leaf_count);

std::vector<Letter> CandidateAlphabet(const std::set<std::string>& atoms);

template <typename Property>
std::size_t PropertyReach(const Property& property);

template <typename Property>
std::size_t SequenceChildReach(const Property& property, std::size_t absent) {
  return property.sequence ? SequenceReach(*property.sequence) : absent;
}

template <typename Property>
std::size_t LhsChildReach(const Property& property, std::size_t absent) {
  return property.lhs ? PropertyReach(*property.lhs) : absent;
}

template <typename Property>
std::size_t RhsChildReach(const Property& property, std::size_t absent) {
  return property.rhs ? PropertyReach(*property.rhs) : absent;
}

template <typename Property>
std::size_t PropertyReach(const Property& property) {
  switch (property.kind) {
    case Property::Kind::kStrong:
    case Property::Kind::kWeak:
      return SequenceChildReach(property, 1);
    case Property::Kind::kParen:
    case Property::Kind::kNot:
      return LhsChildReach(property, 1);
    case Property::Kind::kImplication:
      return SequenceChildReach(property, 0) + LhsChildReach(property, 0);
    case Property::Kind::kOr:
    case Property::Kind::kAnd:
      return std::max(LhsChildReach(property, 0), RhsChildReach(property, 0));
    case Property::Kind::kUntil:
      return LhsChildReach(property, 0) + RhsChildReach(property, 0) + 1;
    case Property::Kind::kNexttime:
    case Property::Kind::kAcceptOn:
      return LhsChildReach(property, 0) + 1;
    default:
      return LhsChildReach(property, 1);
  }
}

template <typename SlicePredicate>
bool SomeWordOfLengthSatisfies(const std::vector<Letter>& alphabet,
                               std::size_t length, const SequenceExpr& seq,
                               SlicePredicate satisfies) {
  const std::size_t kBase = alphabet.size();
  std::size_t total = 1;
  for (std::size_t i = 0; i < length; ++i) {
    total *= kBase;
  }
  for (std::size_t code = 0; code < total; ++code) {
    Word word(length);
    std::size_t rest = code;
    for (std::size_t pos = 0; pos < length; ++pos) {
      word[pos] = alphabet[rest % kBase];
      rest /= kBase;
    }
    if (satisfies(word, length, seq)) {
      return true;
    }
  }
  return false;
}

template <typename SlicePredicate>
bool IsNondegenerateSequenceImpl(const SequenceExpr& sequence,
                                 SlicePredicate slice) {
  std::shared_ptr<const SequenceExpr> owner;
  const SequenceExpr* target = &sequence;
  if (ContainsClock(sequence)) {
    owner = RewriteClockedSequence(sequence);
    target = owner.get();
  }

  std::set<std::string> atoms;
  std::size_t leaf_count = 0;
  CollectSequenceAtoms(*target, atoms, leaf_count);

  const std::vector<Letter> kAlphabet = CandidateAlphabet(atoms);
  const std::size_t kMaxLength = leaf_count + 2;
  for (std::size_t length = 1; length <= kMaxLength; ++length) {
    if (SomeWordOfLengthSatisfies(kAlphabet, length, *target, slice)) {
      return true;
    }
  }
  return false;
}

template <typename TopProperty, typename SatisfiesFn>
bool DisableIffShape(const Word& word, const TopProperty& top,
                     SatisfiesFn satisfies) {
  if (!top.disable_condition || !top.property) {
    return false;
  }
  const std::size_t kI = FirstSatisfyingIndex(word, *top.disable_condition);
  if (kI == word.size()) {
    return false;
  }
  const std::size_t kReach = PropertyReach(*top.property);
  const Word kPrefix = FirstLetters(word, kI);
  const Word kTopCompleted = PrefixWithTail(kPrefix, LetterTop(), kReach);
  const Word kBottomCompleted = PrefixWithTail(kPrefix, LetterBottom(), kReach);
  return satisfies(kTopCompleted, *top.property) &&
         !satisfies(kBottomCompleted, *top.property);
}

template <typename Property, typename NonVacuousFn, typename NeutralFn>
bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const Property& operand, NonVacuousFn non_vacuous,
                          NeutralFn neutrally_satisfies) {
  if (!non_vacuous(word, operand)) {
    return false;
  }
  const std::size_t kFirstB = FirstSatisfyingIndex(word, boolean);
  if (kFirstB == word.size()) {
    return true;
  }
  const std::size_t kReach = PropertyReach(operand);
  for (std::size_t len = 0; len <= kFirstB; ++len) {
    const Word kPrefix = FirstLetters(word, len);
    const Word kBottom = PrefixWithTail(kPrefix, LetterBottom(), kReach);
    const Word kTop = PrefixWithTail(kPrefix, LetterTop(), kReach);
    if (neutrally_satisfies(kBottom, operand) ||
        !neutrally_satisfies(kTop, operand)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
