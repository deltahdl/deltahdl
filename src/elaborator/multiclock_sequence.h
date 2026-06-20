#ifndef DELTA_ELABORATOR_MULTICLOCK_SEQUENCE_H
#define DELTA_ELABORATOR_MULTICLOCK_SEQUENCE_H

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace delta {

// Models the legality of a multiclocked sequence, per IEEE 1800-2023 §16.13.1.
//
// A multiclocked sequence is a concatenation of maximal singly clocked
// subsequences (as produced by the §F.4.1 rewrite), each tagged with the
// clocking event that governs it and the operator that joins it to the
// preceding subsequence.

// The operator joining a subsequence to its predecessor.
enum class MulticlockJoin : std::uint8_t {
  // The subsequence is the first; it has no preceding join.
  kLeading,
  // The subsequence follows a single-delay concatenation (`##1`).
  kSingleDelay,
  // The subsequence follows a zero-delay concatenation (`##0`).
  kZeroDelay,
  // The subsequence follows any other sequence operator.
  kOther,
};

// One maximal singly clocked subsequence of a multiclocked concatenation.
struct MulticlockSubsequence {
  // Identifier of the clocking event governing this subsequence.
  std::string clock;
  // The operator joining this subsequence to the preceding one.
  MulticlockJoin join = MulticlockJoin::kLeading;
  // Whether this subsequence can match the empty word (per §16.9.2.1).
  bool admits_empty = false;
};

// Checks the §16.13.1 legality rules over `subsequences`, which must be in
// source order. Returns std::nullopt when the multiclocked sequence is legal;
// otherwise returns a human-readable description of the first violation.
//
// The two rules enforced once the concatenation crosses a clock boundary are:
//   - every maximal singly clocked subsequence must match only nonempty words;
//   - differently clocked operands may be joined only by `##1` or `##0`.
// A concatenation that stays on a single clock is governed by the ordinary
// singly clocked sequence rules and is not constrained here.
std::optional<std::string> CheckMulticlockSequenceLegality(
    const std::vector<MulticlockSubsequence>& subsequences);

}  // namespace delta

#endif  // DELTA_ELABORATOR_MULTICLOCK_SEQUENCE_H
