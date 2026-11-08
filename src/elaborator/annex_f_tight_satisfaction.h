#pragma once

#include <cstdint>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"

namespace delta {

struct Letter {
  enum class Kind : std::uint8_t {
    kTop,
    kBottom,
    kAtomSet,
  };

  Kind kind = Kind::kAtomSet;
  std::set<std::string> atoms;
};

Letter LetterTop();
Letter LetterBottom();
Letter LetterAtoms(std::set<std::string> atoms);

using Word = std::vector<Letter>;

bool LetterSatisfiesBoolean(const Letter& letter, const BooleanExpr& b);

bool TightlySatisfies(const Word& word, const SequenceExpr& sequence);

bool TightlySatisfiedByEmptyWord(const SequenceExpr& sequence);

bool IsNondegenerateSequence(const SequenceExpr& sequence);

}  // namespace delta
