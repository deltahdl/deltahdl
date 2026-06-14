#include "elaborator/annex_f_future.h"

#include <cstddef>
#include <optional>

#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::optional<std::size_t> FutureGclkSourceIndex(const Word& word,
                                                 std::size_t j) {
  if (word.empty()) {
    return std::nullopt;  // §F.6.3 requires a nonempty word.
  }
  if (j >= word.size() - 1) {
    // §F.6.3 constrains the point to 0 <= j < |w| - 1. At j == |w| - 1 the value
    // is undefined for a finite word, and a larger j lies past the end; neither
    // has a following letter to sample.
    return std::nullopt;
  }
  return j + 1;  // §F.6.3: $future_gclk(e)[w^j] = e[w^{j+1}].
}

bool FutureGclkIsUndefined(const Word& word, std::size_t j) {
  if (word.empty()) {
    return false;
  }
  // §F.6.3: for a finite word, $future_gclk(e)[w^{|w|-1}] is undefined.
  return j == word.size() - 1;
}

}  // namespace delta
