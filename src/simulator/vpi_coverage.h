#pragma once

// IEEE 1800-2023 §40.5 "VPI coverage extensions", and §40.5.2 "Obtaining
// coverage information" within it.
//
// §40.5.2 has no grammar. It describes what a PLI client reads back through
// vpi_get() for the coverage properties enumerated in §40.5.1: how many items
// of a coverage type an instance has covered, whether a particular item is
// covered, and the per-assertion tallies (attempts, successes, vacuous
// successes, disables, kills, failures) that explain that verdict.
//
// The first of those - the number of covered items of a coverage type in an
// instance - is answered by vpi_get() out of the run's own coverage state, in
// vpi_query.cpp, because it is the figure $coverage_get reports for the same
// scope and §40.5 extends §40.2's one coverage API rather than keeping a second
// one. The two routines this file declares are what puts a query or a control
// arriving through VPI into that state's terms.
//
// The remaining query rules are encoded below as small pure helpers over plain
// tally structures so they can be exercised directly. Nothing yet produces the
// per-object tallies they read: recording an assertion's attempts, successes
// and failures as it is evaluated is the collection those properties report on,
// and until the simulator keeps it there is no tally for vpi_get() to hand
// them.

#include <cstdint>
#include <optional>
#include <string>

namespace delta {

struct VpiObject;

// §40.5.1 gives the four coverage types VPI property names of their own and
// §40.3.1 gives the same four the `SV_COV_* macros, while §40.5.3 has the VPI
// operations carry the semantics of the system functions those macros are
// written for. What is named is therefore one coverage of one type reached
// through two doors, and the coverage state is keyed by the §40.3.1 value the
// system functions hand it, so a property arriving through VPI is put into
// those terms before it reaches the state. Absent for an argument naming none
// of the four. Written in vpi_control.cpp, beside the operations that use it.
std::optional<int> CoverageTypeForVpiProperty(int property);

// The scope a coverage handle names: its hierarchical name, or its simple name
// where it carries no hierarchical one. A null handle names no scope, which the
// §40.3.2 rules read as a nonexisting one - a bad argument.
//
// So does a handle that is neither an instance nor an assertion. §40.5.3 writes
// the control over those two kinds and no third, and says why there is no
// third: "Statement, toggle, and FSM coverage are not individually controllable
// (i.e., they are controllable only at the instance level and not on a
// per-statement, signal, or FSM basis)", and §40.5.2 reads the coverage of a
// type out of an instance handle in the same terms. A handle of any other kind
// is the per-object control that sentence rules out rather than a scope to act
// on. Taken off its text alone it was a scope: a signal handle carries a name
// like any other, and toggle coverage is exactly what a coverage engine keeps
// per signal, so a PLI application could start, stop or reset one signal and be
// told `SV_COV_OK for it. Written in vpi_control.cpp.
std::string CoverageScopeName(const VpiObject* scope_handle);

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

// The kind of item a coverage handle denotes, as far as the vpiCoveredMax rule
// is concerned. An assertion handle and an FSM state handle each stand for a
// single coverable entity; the aggregate kinds (a statement block, a signal, or
// a whole FSM) stand for as many entities as the handle holds.
enum class CoverageHandleKind : std::uint8_t {
  kAssertion,
  kFsmState,
  kAggregate,
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
inline std::uint64_t AssertAttemptCovered(const AssertionCoverageCounters& c) {
  return c.attempts;
}

// vpiAssertSuccessCovered: the number of nonvacuous successes of the assertion,
// or, for a cover sequence handle, the number of sequence matches. Both are
// recorded in the same field, so the value is reported uniformly.
inline std::uint64_t AssertSuccessCovered(const AssertionCoverageCounters& c) {
  return c.successes;
}

// vpiAssertVacuousSuccessCovered: the number of vacuous successes.
inline std::uint64_t AssertVacuousSuccessCovered(
    const AssertionCoverageCounters& c) {
  return c.vacuous_successes;
}

// vpiAssertDisableCovered: the number of times the assertion reached the
// disabled state.
inline std::uint64_t AssertDisableCovered(const AssertionCoverageCounters& c) {
  return c.disabled;
}

// vpiAssertKillCovered: the number of times the assertion was killed.
inline std::uint64_t AssertKillCovered(const AssertionCoverageCounters& c) {
  return c.killed;
}

// vpiAssertFailureCovered: the number of failures of the assertion.
inline std::uint64_t AssertFailureCovered(const AssertionCoverageCounters& c) {
  return c.failures;
}

// vpiCovered for an assertion handle: the assertion counts as covered only once
// it has been attempted, has produced at least one nonvacuous success, and has
// never failed.
inline bool AssertionCovered(const AssertionCoverageCounters& c) {
  return c.attempts > 0 && c.successes > 0 && c.failures == 0;
}

// The number of attempts still in progress: attempts that have not yet resolved
// into any terminal outcome (nonvacuous success, vacuous success, disable,
// kill, or failure). This identity does not describe a cover sequence, where a
// single attempt may match many times, so the result is absent for one. Should
// the recorded outcomes ever exceed the attempts the count is clamped to zero.
inline std::optional<std::uint64_t> AssertInProgress(
    const AssertionCoverageCounters& c) {
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
                                          const AssertionCoverageCounters& c) {
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
inline std::uint64_t CoveredEntityCount(const EntityCoverage& e) {
  return e.covered;
}

// vpiCoveredCount: how many times the item has been covered.
inline std::uint64_t CoveredCount(const EntityCoverage& e) {
  return e.hit_count;
}

// vpiCoveredMax: the number of coverable entities the handle points to. For a
// handle that aggregates entities (a block of statements, a signal's bits, or
// an FSM's states) this is the entity total. For an assertion handle or an FSM
// state handle it shall always be 1, regardless of the entity total carried by
// the tally, because such a handle denotes exactly one coverable entity.
inline std::uint64_t CoveredMax(CoverageHandleKind kind,
                                const EntityCoverage& e) {
  switch (kind) {
    case CoverageHandleKind::kAssertion:
    case CoverageHandleKind::kFsmState:
      return 1;
    case CoverageHandleKind::kAggregate:
      return e.total;
  }
  return e.total;
}

// vpi_get(<coverageType>, instance_handle): the number of covered items of the
// requested coverage type within the instance. A property that is not one of
// the four coverage types selects nothing.
inline std::uint64_t InstanceCoverageCount(CoverageProperty property,
                                           const InstanceCoverage& inst) {
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
