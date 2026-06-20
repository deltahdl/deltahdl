#pragma once

// IEEE 1800-2023 §40.5.2 "Obtaining coverage information".
//
// This subclause has no grammar. It describes what a PLI client reads back
// through vpi_get() for the coverage properties enumerated in §40.5.1: how many
// items of a coverage type an instance has covered, whether a particular item
// is covered, and the per-assertion tallies (attempts, successes, vacuous
// successes, disables, kills, failures) that explain that verdict.
//
// The query rules are encoded here as small pure helpers over plain tally
// structures so they can be exercised directly. The simulator's VPI entry
// points feed real per-object tallies into these same helpers when answering a
// vpi_get() call.

#include <cstdint>
#include <optional>

namespace delta {

// The §40.5.1 coverage properties relevant to a coverage query. The four
// *Coverage members are instance-level coverage types; the remaining members
// are per-item or per-assertion status properties. The names mirror the VPI
// constants (vpiAssertCoverage, vpiCovered, ...) without redefining them.
enum class CoverageProperty : std::uint8_t {
  // Instance-level coverage types.
  kAssertCoverage,
  kFsmStateCoverage,
  kStatementCoverage,
  kToggleCoverage,
  // Item-level status.
  kCovered,
  kCoveredCount,
  // Per-assertion status counts.
  kAssertAttemptCovered,
  kAssertSuccessCovered,
  kAssertFailureCovered,
  kAssertVacuousSuccessCovered,
  kAssertDisableCovered,
  kAssertKillCovered,
};

// Running tallies for one assertion's evaluation history. These back the
// per-assertion status properties a client reads from an assertion handle.
//
// When is_cover_sequence is set the handle denotes a cover sequence rather than
// an assertion: successes is then the number of sequence matches (which may
// exceed the number of attempts), and the in-progress identity below does not
// apply because a single attempt can yield many matches.
struct AssertionCoverageCounters {
  std::uint64_t attempts = 0;
  std::uint64_t successes =
      0;  // nonvacuous successes, or matches for a sequence
  std::uint64_t vacuous_successes = 0;
  std::uint64_t disabled = 0;
  std::uint64_t killed = 0;
  std::uint64_t failures = 0;
  bool is_cover_sequence = false;
};

// Coverage of a handle that aggregates several coverable entities, such as the
// statements of a block, the states of an FSM, or the individual bits of a
// signal. total is how many entities the handle holds, covered is how many of
// them are covered, and hit_count is how many times the item has been covered.
struct EntityCoverage {
  std::uint64_t total = 0;
  std::uint64_t covered = 0;
  std::uint64_t hit_count = 0;
};

// Per-instance coverage broken out by coverage type. Each member records how
// many items of that type are covered in the instance.
struct InstanceCoverage {
  EntityCoverage assertions;
  EntityCoverage fsm_states;
  EntityCoverage statements;
  EntityCoverage toggles;
};

// vpiAssertAttemptCovered: the number of attempts of the assertion.
inline std::uint64_t AssertAttemptCovered(const AssertionCoverageCounters &c) {
  return c.attempts;
}

// vpiAssertSuccessCovered: the number of nonvacuous successes of the assertion,
// or, for a cover sequence handle, the number of sequence matches. Both are
// recorded in the same field, so the value is reported uniformly.
inline std::uint64_t AssertSuccessCovered(const AssertionCoverageCounters &c) {
  return c.successes;
}

// vpiAssertVacuousSuccessCovered: the number of vacuous successes.
inline std::uint64_t AssertVacuousSuccessCovered(
    const AssertionCoverageCounters &c) {
  return c.vacuous_successes;
}

// vpiAssertDisableCovered: the number of times the assertion reached the
// disabled state.
inline std::uint64_t AssertDisableCovered(const AssertionCoverageCounters &c) {
  return c.disabled;
}

// vpiAssertKillCovered: the number of times the assertion was killed.
inline std::uint64_t AssertKillCovered(const AssertionCoverageCounters &c) {
  return c.killed;
}

// vpiAssertFailureCovered: the number of failures of the assertion.
inline std::uint64_t AssertFailureCovered(const AssertionCoverageCounters &c) {
  return c.failures;
}

// vpiCovered for an assertion handle: the assertion counts as covered only once
// it has been attempted, has produced at least one nonvacuous success, and has
// never failed.
inline bool AssertionCovered(const AssertionCoverageCounters &c) {
  return c.attempts > 0 && c.successes > 0 && c.failures == 0;
}

// The number of attempts still in progress: attempts that have not yet resolved
// into any terminal outcome (nonvacuous success, vacuous success, disable,
// kill, or failure). This identity does not describe a cover sequence, where a
// single attempt may match many times, so the result is absent for one. Should
// the recorded outcomes ever exceed the attempts the count is clamped to zero.
inline std::optional<std::uint64_t> AssertInProgress(
    const AssertionCoverageCounters &c) {
  if (c.is_cover_sequence) {
    return std::nullopt;
  }
  std::uint64_t resolved =
      c.successes + c.vacuous_successes + c.disabled + c.killed + c.failures;
  if (resolved >= c.attempts) {
    return std::uint64_t{0};
  }
  return c.attempts - resolved;
}

// Dispatches an assertion-status property to the matching tally. Properties
// that are not per-assertion status counts contribute nothing.
inline std::uint64_t AssertionStatusQuery(CoverageProperty property,
                                          const AssertionCoverageCounters &c) {
  switch (property) {
    case CoverageProperty::kAssertAttemptCovered:
      return AssertAttemptCovered(c);
    case CoverageProperty::kAssertSuccessCovered:
      return AssertSuccessCovered(c);
    case CoverageProperty::kAssertVacuousSuccessCovered:
      return AssertVacuousSuccessCovered(c);
    case CoverageProperty::kAssertDisableCovered:
      return AssertDisableCovered(c);
    case CoverageProperty::kAssertKillCovered:
      return AssertKillCovered(c);
    case CoverageProperty::kAssertFailureCovered:
      return AssertFailureCovered(c);
    default:
      return 0;
  }
}

// vpiCovered for a handle that holds several coverable entities: how many of
// those entities are covered (covered statements, FSM states, or signal bits).
inline std::uint64_t CoveredEntityCount(const EntityCoverage &e) {
  return e.covered;
}

// vpiCoveredCount: how many times the item has been covered.
inline std::uint64_t CoveredCount(const EntityCoverage &e) {
  return e.hit_count;
}

// vpi_get(<coverageType>, instance_handle): the number of covered items of the
// requested coverage type within the instance. A property that is not one of
// the four coverage types selects nothing.
inline std::uint64_t InstanceCoverageCount(CoverageProperty property,
                                           const InstanceCoverage &inst) {
  switch (property) {
    case CoverageProperty::kAssertCoverage:
      return CoveredEntityCount(inst.assertions);
    case CoverageProperty::kFsmStateCoverage:
      return CoveredEntityCount(inst.fsm_states);
    case CoverageProperty::kStatementCoverage:
      return CoveredEntityCount(inst.statements);
    case CoverageProperty::kToggleCoverage:
      return CoveredEntityCount(inst.toggles);
    default:
      return 0;
  }
}

}  // namespace delta
