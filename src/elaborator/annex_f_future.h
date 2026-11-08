#pragma once

#include <cstddef>
#include <optional>
#include <string>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::optional<std::size_t> FutureGclkSourceIndex(const Word& word,
                                                 std::size_t j);

bool FutureGclkIsUndefined(const Word& word, std::size_t j);

ExtendedExpression FutureGclkOfAtomOnCompletion(const std::string& name,
                                                const Letter& tail);

}  // namespace delta
