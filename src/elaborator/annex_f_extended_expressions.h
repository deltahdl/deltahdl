#pragma once

#include <cstddef>
#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

using ExtendedExpression =
    std::function<std::optional<bool>(const Word& word, std::size_t j)>;

ExtendedExpression AtomAsExtendedExpression(const std::string& name);

ExtendedExpression PastGclkOfAtom(const std::string& name, bool initial);

ExtendedExpression FutureGclkOfAtom(const std::string& name);

Word WordWithExtendedAtom(const Word& word, const std::string& name,
                          const ExtendedExpression& e);

bool DependsOnOtherLetters(const ExtendedExpression& e, const Word& word,
                           std::size_t j, const std::vector<Word>& others);

}  // namespace delta
