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

// Internal helpers shared by the Annex F satisfaction layers (§F.5.2 / §F.5.3 /
// §F.5.5 / §F.5.6). These are the generic word, letter, and alphabet utilities
// that the vacuity, neutral-satisfaction, and tight-satisfaction translation
// units -- in both their plain and local-variable forms -- would otherwise each
// copy verbatim. The non-template functions are declared here and defined once
// in annex_f_vacuity.cpp; the templates are header-only and instantiated per
// caller with the property type or slice/satisfaction policy that differs
// between layers.

namespace delta {

// §F.5 (page 1246): w-bar interchanges T and _|_; a letter in 2^P is unchanged.
Letter ComplementLetter(const Letter& letter);

// §F.5: w-bar, the letterwise complement of the whole word.
Word ComplementWord(const Word& word);

// §F.5: w^{i.}, the word with its first i letters deleted (empty once i reaches
// the length of w).
Word Suffix(const Word& word, std::size_t i);

// §F.5: w^{0,k}, the finite prefix w^0 w^1 ... w^k (the first k+1 letters).
Word PrefixInclusive(const Word& word, std::size_t k);

// §F.5: the first i letters of w; the empty word when i = 0.
Word FirstLetters(const Word& word, std::size_t i);

// The least index at which a letter of the word satisfies b, or word.size() if
// no letter does. With b never satisfied this equals |w|, which is exactly the
// "for every 0 <= i < |w|, w^i |/= b" condition the abort/disable rules use.
std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b);

// A structural bound on how far a sequence can reach into a word, mirroring the
// bound §F.5.3.1 uses: enough tail letters past an explicit prefix that
// extending a constant T^omega / _|_^omega tail cannot change a tight match.
std::size_t SequenceReach(const SequenceExpr& seq);

// A finite materialization of a prefix followed by a constant tail (T^omega or
// _|_^omega), padded `reach` letters past the prefix plus a margin -- enough
// for the verdict to have stabilized for the finite properties this model
// handles, matching §F.5.3.1's PrefixWithTail.
Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach);

// Collect the atomic propositions named by a Boolean expression.
void CollectAtoms(const BooleanExpr& b, std::set<std::string>& out);

// Collect the atoms mentioned by a sequence and count its match-bearing leaves,
// bounding the nondegeneracy witness search.
void CollectSequenceAtoms(const SequenceExpr& seq, std::set<std::string>& out,
                          std::size_t& leaf_count);

// Build the candidate alphabet for the witness search: T, _|_, and every subset
// of the mentioned atoms. The subset enumeration is capped so the search stays
// finite; that is ample for the sequences this model evaluates.
std::vector<Letter> CandidateAlphabet(const std::set<std::string>& atoms);

template <typename Property>
std::size_t PropertyReach(const Property& property);

// The reach contributed by a property's optional embedded sequence: its
// SequenceReach when present, otherwise `absent`. Factoring the optional-child
// ternaries out of PropertyReach keeps that switch's per-case arms flat.
template <typename Property>
std::size_t SequenceChildReach(const Property& property, std::size_t absent) {
  return property.sequence ? SequenceReach(*property.sequence) : absent;
}

// The reach of a property's optional left operand: PropertyReach of it when
// present, otherwise `absent`.
template <typename Property>
std::size_t LhsChildReach(const Property& property, std::size_t absent) {
  return property.lhs ? PropertyReach(*property.lhs) : absent;
}

// The reach of a property's optional right operand: PropertyReach of it when
// present, otherwise `absent`.
template <typename Property>
std::size_t RhsChildReach(const Property& property, std::size_t absent) {
  return property.rhs ? PropertyReach(*property.rhs) : absent;
}

// A structural bound on how far a property can reach into a word; once a word's
// suffix lies entirely inside a constant tail this many letters past the
// explicit prefix, extending the tail cannot change the verdict. Templated on
// the property type so the plain (§F.5.3) and local-variable (§F.5.6) forms
// share one definition; the local-variable property's extra kLocalVarDecl form
// falls through to the same kParen/kNot body via the default label.
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
      // §F.5.6's local-variable declaration form ( t v ; P ) reaches as far as
      // its body, exactly like the parenthesized form above.
      return LhsChildReach(property, 1);
  }
}

// The witness search of §F.5.2 / §F.5.5: does some word of `length` over
// `alphabet` satisfy `seq`? Templated on the slice predicate so the plain layer
// can pass tight satisfaction and the local-variable layer can pass the
// nonempty output-context test.
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

// §F.5.5 (and §F.5.6.5): a sequence is nondegenerate iff some word over its
// candidate alphabet tightly matches it. The witness search is identical
// across the plain and local-variable layers; only the per-word slice test
// differs, so it is passed in as a predicate. Mirrors §F.5.5's bounded search.
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

// §F.5.3.1 (and §F.5.6.1): T = disable iff (b) P disables on w iff some letter
// of w satisfies b and, for i the least such index, w^{0,i-1} T^omega |= P and
// w^{0,i-1} _|_^omega |/= P. Templated on the top-level property type plus the
// satisfaction policy so the plain and local-variable (LocalContext-threading)
// layers share one body.
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

// §F.5.3.3 (and §F.5.6.3): the abort/disable family shares one shape. The
// property w |=^non OP(b) P holds iff w |=^non P and one of: (1) no letter of w
// satisfies b; or (2) some b-free prefix x of w leaves P unmet under one of the
// constant tails x _|_^omega / x T^omega. accept_on (b) P and disable iff (b) P
// both use this rule. Templated on the property type plus a non-vacuity policy
// and a neutral-satisfaction policy so the plain and local-variable layers --
// the latter threading a LocalContext through both policies -- share one body.
template <typename Property, typename NonVacuousFn, typename NeutralFn>
bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const Property& operand, NonVacuousFn non_vacuous,
                          NeutralFn neutrally_satisfies) {
  if (!non_vacuous(word, operand)) {
    return false;
  }
  const std::size_t kFirstB = FirstSatisfyingIndex(word, boolean);
  // (1) No letter of w satisfies b.
  if (kFirstB == word.size()) {
    return true;
  }
  // (2) Some b-free prefix x leaves P unmet under one of the constant tails.
  // The prefixes with no b-letter are exactly those of length 0..kFirstB.
  const std::size_t kReach = PropertyReach(operand);
  for (std::size_t len = 0; len <= kFirstB; ++len) {
    const Word kPrefix = FirstLetters(word, len);
    const Word kBottom = PrefixWithTail(kPrefix, LetterBottom(), kReach);
    const Word kTop = PrefixWithTail(kPrefix, LetterTop(), kReach);
    if (!neutrally_satisfies(kBottom, operand) ||
        !neutrally_satisfies(kTop, operand)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
