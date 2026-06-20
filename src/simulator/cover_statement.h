#pragma once

// IEEE 1800-2023 §16.14.3 "Cover statement".
//
// A cover statement comes in two categories. A `cover property` statement
// monitors property coverage, where the coverage count rises at most once per
// evaluation attempt; a `cover sequence` statement monitors sequence coverage,
// where every match of the sequence in an attempt is counted with multiplicity.
// Both feed running tallies that a client reads back through the §40.5.2
// coverage API; the rules here say how a single attempt updates those tallies
// and how often the optional pass statement runs.
//
// The rules are encoded as small pure helpers over plain outcome descriptions
// so the canonical test can exercise them directly. The simulator's
// cover-statement evaluation path applies these same helpers to real
// per-attempt outcomes.

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

// §16.14.3: the two categories of cover statement. `cover property` records
// property coverage; `cover sequence` records sequence coverage.
enum class CoverStatementCategory : uint8_t {
  kProperty,
  kSequence,
};

// §16.14.3: the outcome of one evaluation attempt of a `cover property`
// statement's underlying property_spec, in the terms its result counters care
// about. An attempt is disabled, succeeds nonvacuously, succeeds vacuously, or
// does none of these (an ordinary nonsuccess).
struct CoverPropertyAttemptOutcome {
  bool disabled = false;
  bool nonvacuous_success = false;
  bool vacuous_success = false;
};

// §16.14.3: the attempt counter for a `cover property` rises by one for every
// evaluation attempt, including the attempts that result in a disabled
// evaluation. Returns the increment contributed by one attempt.
inline std::uint64_t CoverPropertyAttemptDelta(
    const CoverPropertyAttemptOutcome& /*outcome*/) {
  return 1;
}

// §16.14.3: the success counter excludes disabled evaluations and is
// incremented at most once per evaluation attempt — a property succeeds at most
// once per attempt, so this never exceeds one. Counts nonvacuous successes.
inline std::uint64_t CoverPropertySuccessDelta(
    const CoverPropertyAttemptOutcome& outcome) {
  return (!outcome.disabled && outcome.nonvacuous_success) ? 1 : 0;
}

// §16.14.3: the vacuous-success counter likewise excludes disabled evaluations
// and rises at most once per attempt. Counts successes that hold by vacuity.
inline std::uint64_t CoverPropertyVacuousSuccessDelta(
    const CoverPropertyAttemptOutcome& outcome) {
  return (!outcome.disabled && outcome.vacuous_success) ? 1 : 0;
}

// §16.14.3: the pass statement of a `cover property` runs once for each
// successful evaluation attempt of the underlying property_spec. A disabled
// evaluation is not a success, so it triggers no pass statement. Returns how
// many times the pass statement runs for one attempt (zero or one).
inline std::uint64_t CoverPropertyPassExecutions(
    const CoverPropertyAttemptOutcome& outcome) {
  if (outcome.disabled) return 0;
  return (outcome.nonvacuous_success || outcome.vacuous_success) ? 1 : 0;
}

// §16.14.3: the results for a `cover sequence` include the number of times
// attempted; the attempt counter rises by one for each evaluation attempt of
// the cover sequence statement. Returns the increment contributed by one
// attempt.
inline std::uint64_t CoverSequenceAttemptDelta() { return 1; }

// §16.14.3: in a `cover sequence`, a completed match counts toward the attempt
// total only when it completes without the disable iff condition having
// occurred. Returns whether such a match is counted.
inline bool CoverSequenceMatchCounts(bool disable_iff_occurred) {
  return !disable_iff_occurred;
}

// §16.14.3: the number of times matched for one attempt of a `cover sequence`.
// Every match of the sequence_expr that completes without the disable iff
// condition is counted, with multiplicity; no other match contributes. The
// argument lists, for each completed match in the attempt, whether the disable
// iff condition had occurred by the time it completed.
inline std::uint64_t CoverSequenceMatchDelta(
    const std::vector<bool>& completed_match_disable_iff_occurred) {
  std::uint64_t matched = 0;
  for (bool disable_iff_occurred : completed_match_disable_iff_occurred) {
    if (CoverSequenceMatchCounts(disable_iff_occurred)) ++matched;
  }
  return matched;
}

// §16.14.3: the pass statement of a `cover sequence` runs, with multiplicity,
// once for each match counted toward the attempt total — equivalently, once per
// execution of increment_match_coverage() in the equivalent assert property.
// Returns how many times the pass statement runs for one attempt.
inline std::uint64_t CoverSequencePassExecutions(
    const std::vector<bool>& completed_match_disable_iff_occurred) {
  return CoverSequenceMatchDelta(completed_match_disable_iff_occurred);
}

// §16.14.3: the pass statement of either cover category executes in the
// Reactive region of the time step in which the corresponding attempt succeeds
// or match completes.
inline Region CoverPassStatementRegion() { return Region::kReactive; }

}  // namespace delta
