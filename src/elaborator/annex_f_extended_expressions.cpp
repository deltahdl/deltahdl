#include "elaborator/annex_f_extended_expressions.h"

#include <cstddef>
#include <optional>
#include <string>
#include <vector>

#include "elaborator/annex_f_future.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_past.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {
namespace {

// Two letters are the same when they are of one kind and, for atom sets,
// carry the same atoms.
bool SameLetter(const Letter& lhs, const Letter& rhs) {
  return lhs.kind == rhs.kind &&
         (lhs.kind != Letter::Kind::kAtomSet || lhs.atoms == rhs.atoms);
}

}  // namespace

ExtendedExpression AtomAsExtendedExpression(const std::string& name) {
  return [name](const Word& word, std::size_t j) -> std::optional<bool> {
    if (j >= word.size()) {
      return std::nullopt;
    }
    return LetterSatisfiesBoolean(word[j], *BoolAtom(name));
  };
}

ExtendedExpression PastGclkOfAtom(const std::string& name, bool initial) {
  // §F.6.2: e[w^{j-1}] for j > 0, and the initial value at w^0.
  return
      [name, initial](const Word& word, std::size_t j) -> std::optional<bool> {
        if (j >= word.size()) {
          return std::nullopt;
        }
        const std::optional<std::size_t> kSource = PastGclkSourceIndex(word, j);
        if (!kSource) {
          return initial;
        }
        return LetterSatisfiesBoolean(word[*kSource], *BoolAtom(name));
      };
}

ExtendedExpression FutureGclkOfAtom(const std::string& name) {
  // §F.6.3: e[w^{j+1}] where a following letter exists, undefined otherwise.
  return [name](const Word& word, std::size_t j) -> std::optional<bool> {
    const std::optional<std::size_t> kSource = FutureGclkSourceIndex(word, j);
    if (!kSource) {
      return std::nullopt;
    }
    return LetterSatisfiesBoolean(word[*kSource], *BoolAtom(name));
  };
}

Word WordWithExtendedAtom(const Word& word, const std::string& name,
                          const ExtendedExpression& e) {
  Word out = word;
  for (std::size_t j = 0; j < out.size(); ++j) {
    if (out[j].kind != Letter::Kind::kAtomSet) {
      continue;
    }
    const std::optional<bool> kValue = e(word, j);
    if (!kValue) {
      continue;
    }
    if (*kValue) {
      out[j].atoms.insert(name);
    } else {
      out[j].atoms.erase(name);
    }
  }
  return out;
}

bool DependsOnOtherLetters(const ExtendedExpression& e, const Word& word,
                           std::size_t j, const std::vector<Word>& others) {
  if (j >= word.size()) {
    return false;
  }
  const std::optional<bool> kHere = e(word, j);
  for (const Word& other : others) {
    if (j >= other.size() || !SameLetter(word[j], other[j])) {
      continue;
    }
    if (e(other, j) != kHere) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
