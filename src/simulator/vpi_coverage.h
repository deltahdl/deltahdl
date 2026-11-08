#pragma once

#include <cstdint>
#include <optional>
#include <string>

namespace delta {

struct VpiObject;

std::optional<int> CoverageTypeForVpiProperty(int property);

std::string CoverageScopeName(const VpiObject* scope_handle);

enum class CoverageProperty : std::uint8_t {
  kAssertCoverage,
  kFsmStateCoverage,
  kStatementCoverage,
  kToggleCoverage,
  kCovered,
  kCoveredCount,
  kAssertAttemptCovered,
  kAssertSuccessCovered,
  kAssertFailureCovered,
  kAssertVacuousSuccessCovered,
  kAssertDisableCovered,
  kAssertKillCovered,
};

std::optional<CoverageProperty> CoveragePropertyFromVpi(int property);

struct AssertionCoverageCounters {
  std::uint64_t attempts = 0;
  std::uint64_t successes = 0;
  std::uint64_t vacuous_successes = 0;
  std::uint64_t disabled = 0;
  std::uint64_t killed = 0;
  std::uint64_t failures = 0;
  bool is_cover_sequence = false;
};

struct EntityCoverage {
  std::uint64_t total = 0;
  std::uint64_t covered = 0;
  std::uint64_t hit_count = 0;
};

enum class CoverageHandleKind : std::uint8_t {
  kAssertion,
  kFsmState,
  kAggregate,
};

struct InstanceCoverage {
  EntityCoverage assertions;
  EntityCoverage fsm_states;
  EntityCoverage statements;
  EntityCoverage toggles;
};

inline std::uint64_t AssertAttemptCovered(const AssertionCoverageCounters& c) {
  return c.attempts;
}

inline std::uint64_t AssertSuccessCovered(const AssertionCoverageCounters& c) {
  return c.successes;
}

inline std::uint64_t AssertVacuousSuccessCovered(
    const AssertionCoverageCounters& c) {
  return c.vacuous_successes;
}

inline std::uint64_t AssertDisableCovered(const AssertionCoverageCounters& c) {
  return c.disabled;
}

inline std::uint64_t AssertKillCovered(const AssertionCoverageCounters& c) {
  return c.killed;
}

inline std::uint64_t AssertFailureCovered(const AssertionCoverageCounters& c) {
  return c.failures;
}

inline bool AssertionCovered(const AssertionCoverageCounters& c) {
  return c.attempts > 0 && c.successes > 0 && c.failures == 0;
}

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

inline std::uint64_t CoveredEntityCount(const EntityCoverage& e) {
  return e.covered;
}

inline std::uint64_t CoveredCount(const EntityCoverage& e) {
  return e.hit_count;
}

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
