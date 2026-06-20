#pragma once

#include <cstdint>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"

namespace delta {

// §F.5 fixes the alphabet Sigma = 2^P U {T, _|_} over which the semantic words
// are formed: each letter is either a set of atomic propositions, the top
// letter T (which satisfies every Boolean expression), or the bottom letter
// _|_ (which satisfies none).
struct Letter {
  enum class Kind : std::uint8_t {
    kTop,      // T -- satisfies every Boolean expression
    kBottom,   // _|_ -- satisfies no Boolean expression
    kAtomSet,  // an element of 2^P
  };

  Kind kind = Kind::kAtomSet;
  std::set<std::string> atoms;  // valid when kind == kAtomSet
};

Letter LetterTop();
Letter LetterBottom();
Letter LetterAtoms(std::set<std::string> atoms);

using Word = std::vector<Letter>;

// §F.5: the satisfaction relation zeta |= b for a single letter. For a letter
// in 2^P a Boolean expression holds when its propositions evaluate to true
// under that set; T |= b for every b and _|_ |= b for no b.
bool LetterSatisfiesBoolean(const Letter& letter, const BooleanExpr& b);

// §F.5.2: tight satisfaction, w |== R, for an unclocked sequence without local
// variables. When the sequence is clocked it is first reduced to its unclocked
// form by the §F.5.1.1 rewrite rules, per "If S is a clocked sequence, then
// w |== S iff w |== S'".
bool TightlySatisfies(const Word& word, const SequenceExpr& sequence);

// §F.3.2's strong/weak sequence forms require that the sequence operand "shall
// not be tightly satisfied by the empty word". This evaluates that predicate.
bool TightlySatisfiedByEmptyWord(const SequenceExpr& sequence);

// §F.5.2: an unclocked sequence is nondegenerate iff some nonempty finite word
// tightly satisfies it; a clocked sequence is nondegenerate iff its unclocked
// rewrite is. The witness search is bounded, which is exact for the finite
// sequences this model is exercised on.
bool IsNondegenerateSequence(const SequenceExpr& sequence);

}  // namespace delta
