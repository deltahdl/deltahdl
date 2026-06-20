#pragma once

#include <algorithm>
#include <cstddef>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
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
      return property.sequence ? SequenceReach(*property.sequence) : 1;
    case Property::Kind::kParen:
    case Property::Kind::kNot:
      return property.lhs ? PropertyReach(*property.lhs) : 1;
    case Property::Kind::kImplication:
      return (property.sequence ? SequenceReach(*property.sequence) : 0) +
             (property.lhs ? PropertyReach(*property.lhs) : 0);
    case Property::Kind::kOr:
    case Property::Kind::kAnd:
      return std::max(property.lhs ? PropertyReach(*property.lhs) : 0,
                      property.rhs ? PropertyReach(*property.rhs) : 0);
    case Property::Kind::kUntil:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) +
             (property.rhs ? PropertyReach(*property.rhs) : 0) + 1;
    case Property::Kind::kNexttime:
    case Property::Kind::kAcceptOn:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) + 1;
    default:
      // §F.5.6's local-variable declaration form ( t v ; P ) reaches as far as
      // its body, exactly like the parenthesized form above.
      return property.lhs ? PropertyReach(*property.lhs) : 1;
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
  const std::size_t base = alphabet.size();
  std::size_t total = 1;
  for (std::size_t i = 0; i < length; ++i) {
    total *= base;
  }
  for (std::size_t code = 0; code < total; ++code) {
    Word word(length);
    std::size_t rest = code;
    for (std::size_t pos = 0; pos < length; ++pos) {
      word[pos] = alphabet[rest % base];
      rest /= base;
    }
    if (satisfies(word, length, seq)) {
      return true;
    }
  }
  return false;
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
    if (!neutrally_satisfies(bottom, operand) ||
        !neutrally_satisfies(top, operand)) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
