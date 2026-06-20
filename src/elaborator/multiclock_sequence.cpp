#include "elaborator/multiclock_sequence.h"

#include <cstddef>

namespace delta {

// §16.13.1: legality of a multiclocked sequence built from its maximal singly
// clocked subsequences.
//
// The cross-clock restrictions only apply once the concatenation actually
// spans more than one clocking event. A run of subsequences that all share a
// single clock collapses to a singly clocked sequence, which is governed by the
// ordinary singly clocked rules rather than the ones below.

namespace {

// True when more than one distinct clocking event governs the subsequences.
bool SpansMultipleClocks(
    const std::vector<MulticlockSubsequence>& subsequences) {
  for (std::size_t i = 1; i < subsequences.size(); ++i) {
    if (subsequences[i].clock != subsequences.front().clock) {
      return true;
    }
  }
  return false;
}

}  // namespace

std::optional<std::string> CheckMulticlockSequenceLegality(
    const std::vector<MulticlockSubsequence>& subsequences) {
  if (!SpansMultipleClocks(subsequences)) {
    return std::nullopt;
  }

  for (std::size_t i = 0; i < subsequences.size(); ++i) {
    const MulticlockSubsequence& subsequence = subsequences[i];

    // Every maximal singly clocked subsequence of a cross-clock concatenation
    // must admit only nonempty matches. An empty match would leave the
    // clocking event at the join ambiguous, since either neighbouring clock
    // could supply the ending tick.
    if (subsequence.admits_empty) {
      return "a maximal singly clocked subsequence of a multiclocked sequence "
             "may not match the empty word";
    }

    // The first subsequence has no preceding join to validate.
    if (i == 0) {
      continue;
    }

    // Across a clock boundary, only the single-delay (`##1`) and zero-delay
    // (`##0`) operators may join two subsequences. An identically clocked join
    // stays in a singly clocked context and is left to the singly clocked
    // rules.
    const bool crosses_clock = subsequence.clock != subsequences[i - 1].clock;
    if (crosses_clock && subsequence.join == MulticlockJoin::kOther) {
      return "differently clocked sequence operands may be joined only by the "
             "single-delay (##1) or zero-delay (##0) operator";
    }
  }

  return std::nullopt;
}

}  // namespace delta
