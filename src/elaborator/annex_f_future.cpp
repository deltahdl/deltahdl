#include "elaborator/annex_f_future.h"

#include <cstddef>
#include <optional>
#include <string>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::optional<std::size_t> FutureGclkSourceIndex(const Word& word,
                                                 std::size_t j) {
  if (word.empty()) {
    return std::nullopt;
  }
  if (j >= word.size() - 1) {
    return std::nullopt;
  }
  return j + 1;
}

bool FutureGclkIsUndefined(const Word& word, std::size_t j) {
  if (word.empty()) {
    return false;
  }
  return j == word.size() - 1;
}

ExtendedExpression FutureGclkOfAtomOnCompletion(const std::string& name,
                                                const Letter& tail) {
  return [name, tail](const Word& word, std::size_t j) -> std::optional<bool> {
    const std::optional<std::size_t> kSource = FutureGclkSourceIndex(word, j);
    if (kSource) {
      return LetterSatisfiesBoolean(word[*kSource], *BoolAtom(name));
    }
    return LetterSatisfiesBoolean(tail, *BoolAtom(name));
  };
}

}  // namespace delta
