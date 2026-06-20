#pragma once

#include <cstddef>
#include <optional>

#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.6.3 fixes the meaning of the "future" extended expression $future_gclk at
// a point w^j of a word over Sigma. Like the "past" expression $past_gclk of
// §F.6.2 it reaches to an adjacent letter, but in the opposite direction: the
// value at j is the value the expression e takes at the immediately following
// letter w^{j+1}. The abstract word semantics determines which letter supplies
// the value (the source index); the actual value e[w^{j+1}] belongs to the type
// system and is out of scope for this model.

// §F.6.3: the source letter index of $future_gclk(e)[w^j]. The value is
// e[w^{j+1}], so the source is the immediately following letter j+1. §F.6.3
// constrains the point to 0 <= j < |w| - 1, the positions that have a following
// letter; std::nullopt at the last letter of a finite word (where §F.6.3 leaves
// the value undefined) and for any j at or past the end of the word.
std::optional<std::size_t> FutureGclkSourceIndex(const Word& word,
                                                 std::size_t j);

// §F.6.3: true exactly at the point where $future_gclk(e)[w^j] is undefined for
// a finite word -- the last letter, j == |w| - 1, which has no following letter
// to sample. This is distinct from a point that lies past the end of the word
// (outside the rule's domain): it is the position the rule names as undefined.
bool FutureGclkIsUndefined(const Word& word, std::size_t j);

}  // namespace delta
