#include "elaborator/annex_f_past.h"

#include <cstddef>
#include <memory>
#include <optional>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

namespace {

// The finite subword w^{lo,hi-1}: letters lo through hi-1 inclusive, i.e. the
// half-open slice [lo, hi) of `word`. §F.6.2 reasons over the subword w^{i,j}
// ending at the point j.
Word Subword(const Word& word, std::size_t lo, std::size_t hi) {
  return Word(word.begin() + static_cast<std::ptrdiff_t>(lo),
              word.begin() + static_cast<std::ptrdiff_t>(hi));
}

// The §F.6.2 gating sequence (c && e2) ##1 (c && e2)[=n-1] ##1 1, expressed in
// the §F.3.2 primitives the tight-satisfaction engine understands. With `g` the
// active condition c && e2, a run of inactive letters is (!g)[*0:$], and the
// nonconsecutive repetition g[=m] expands per §F.3.4.2.3 to g[->m] ##1
// (!g)[*0:$] with g[->m] the m-fold concatenation of ((!g)[*0:$] ##1 g).
// Because the engine reads ##1 as plain adjacency, the whole sequence lays out
// as a leading active letter, then m more active letters each preceded by an
// inactive run, a final trailing inactive run, and one wildcard letter at j --
// exactly n active ticks before j.
std::shared_ptr<const SequenceExpr> GatingSequence(
    const std::shared_ptr<const BooleanExpr>& g, unsigned int n) {
  const std::shared_ptr<const SequenceExpr> active = SeqBoolean(g);
  const std::shared_ptr<const SequenceExpr> inactive_run =
      SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(g)));

  // g[=n-1]. For n == 1 there is no g[->m] part: g[=0] is just a run of
  // inactive letters.
  std::shared_ptr<const SequenceExpr> nonconsecutive = inactive_run;
  const unsigned int repeats = n - 1;
  if (repeats > 0) {
    // g[->repeats]: repeats copies of ((!g)[*0:$] ##1 g) laid end to end.
    const std::shared_ptr<const SequenceExpr> goto_unit =
        SeqConcat(inactive_run, active);
    std::shared_ptr<const SequenceExpr> goto_m = goto_unit;
    for (unsigned int k = 1; k < repeats; ++k) {
      goto_m = SeqConcat(goto_m, goto_unit);
    }
    // g[=repeats] = g[->repeats] ##1 (!g)[*0:$].
    nonconsecutive = SeqConcat(goto_m, inactive_run);
  }

  // (c && e2) ##1 g[=n-1] ##1 1.
  return SeqConcat(active, SeqConcat(nonconsecutive, SeqBoolean(BoolTrue())));
}

}  // namespace

std::vector<std::size_t> PastSourceIndices(
    const Word& word, std::size_t j, unsigned int n,
    const std::shared_ptr<const BooleanExpr>& gate,
    const std::shared_ptr<const BooleanExpr>& clock) {
  std::vector<std::size_t> result;
  if (j >= word.size()) {
    return result;  // §F.6.2 requires 0 <= j < |w|.
  }
  if (n < 1) {
    return result;  // §F.6.2: Let n >= 1.
  }
  // The active condition c && e2, both the destination clock and the gating
  // expression holding.
  const std::shared_ptr<const BooleanExpr> active = BoolAnd(clock, gate);
  const std::shared_ptr<const SequenceExpr> gating = GatingSequence(active, n);
  // §F.6.2: try every start point 0 <= i < j; the subword w^{i,j} must tightly
  // satisfy the gating sequence.
  for (std::size_t i = 0; i < j; ++i) {
    const Word slice = Subword(word, i, j + 1);
    if (TightlySatisfies(slice, *gating)) {
      result.push_back(i);
    }
  }
  return result;
}

bool PastSamplesInitialValue(const Word& word, std::size_t j, unsigned int n,
                             const std::shared_ptr<const BooleanExpr>& gate,
                             const std::shared_ptr<const BooleanExpr>& clock) {
  if (j >= word.size() || n < 1) {
    return false;  // Outside the rule's domain; not the "Otherwise" branch.
  }
  return PastSourceIndices(word, j, n, gate, clock).empty();
}

std::optional<std::size_t> PastGclkSourceIndex(const Word& word,
                                               std::size_t j) {
  if (j >= word.size()) {
    return std::nullopt;  // §F.6.2 requires 0 <= j < |w|.
  }
  if (j == 0) {
    return std::nullopt;  // §F.6.2: at w^0, $past_gclk takes the initial value.
  }
  return j - 1;  // §F.6.2: $past_gclk(e)[w^j] = e[w^{j-1}] for j > 0.
}

}  // namespace delta
