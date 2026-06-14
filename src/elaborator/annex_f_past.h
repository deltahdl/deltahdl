#pragma once

#include <cstddef>
#include <memory>
#include <optional>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.6.2 fixes the meaning of the two "past" extended expressions -- $past and
// $past_gclk -- at a point w^j of a word over Sigma. Like the extended Booleans
// of §F.6.1, the value at j is defined by reaching back to an earlier letter
// w^i; here that earlier letter supplies the value the expression reports. The
// abstract word semantics determines which earlier letter i is selected (the
// source index); the actual value e[w^i], and the initial value used when no
// such i exists, belong to the type system (6.8, Table 6-7) and are out of
// scope for this model.

// §F.6.2 ($past): the source letter indices i, with 0 <= i < j, such that the
// subword w^{i,j} tightly satisfies the gating sequence
//   (c && e2) ##1 (c && e2)[=n-1] ##1 1
// from the empty contexts. The active condition is c && e2 (the destination
// clock c and the gating expression e2 both holding); the sequence pins i to the
// start of a window holding exactly n active ticks, so i is the n-th active tick
// counted back from j. $past(e1, n, e2, c)[w^j] reports e1[w^i] for such an i.
// The result is empty when no index qualifies; §F.6.2 then evaluates e1 at its
// initial values instead. n shall be at least 1; the result is empty when it is
// not, or when j lies outside 0 <= j < |w|.
std::vector<std::size_t> PastSourceIndices(
    const Word& word, std::size_t j, unsigned int n,
    const std::shared_ptr<const BooleanExpr>& gate,
    const std::shared_ptr<const BooleanExpr>& clock);

// §F.6.2 ($past) "Otherwise" branch: true when j lies in 0 <= j < |w| and
// n >= 1 yet no source index qualifies, so $past(e1, n, e2, c)[w^j] takes the
// initial value of e1 rather than a sampled letter.
bool PastSamplesInitialValue(const Word& word, std::size_t j, unsigned int n,
                             const std::shared_ptr<const BooleanExpr>& gate,
                             const std::shared_ptr<const BooleanExpr>& clock);

// §F.6.2 ($past_gclk): the source letter index of $past_gclk(e)[w^j]. The value
// is e[w^{j-1}] when j > 0, so the source is the immediately preceding letter
// j-1; std::nullopt at w^0 (and for an out-of-range j), where §F.6.2 evaluates e
// at its initial values.
std::optional<std::size_t> PastGclkSourceIndex(const Word& word, std::size_t j);

}  // namespace delta
