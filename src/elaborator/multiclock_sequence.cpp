#include "elaborator/multiclock_sequence.h"

#include <cstddef>
#include <optional>
#include <string>
#include <vector>

namespace delta {

namespace {

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

    if (subsequence.admits_empty) {
      return "a maximal singly clocked subsequence of a multiclocked sequence "
             "may not match the empty word";
    }

    if (i == 0) {
      continue;
    }

    const bool kCrossesClock = subsequence.clock != subsequences[i - 1].clock;
    if (kCrossesClock && subsequence.join == MulticlockJoin::kOther) {
      return "differently clocked sequence operands may be joined only by the "
             "single-delay (##1) or zero-delay (##0) operator";
    }
  }

  return std::nullopt;
}

}  // namespace delta
