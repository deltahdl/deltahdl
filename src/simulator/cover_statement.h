#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

enum class CoverStatementCategory : uint8_t {
  kProperty,
  kSequence,
};

struct CoverPropertyAttemptOutcome {
  bool disabled = false;
  bool nonvacuous_success = false;
  bool vacuous_success = false;
};

inline std::uint64_t CoverPropertyAttemptDelta(
    const CoverPropertyAttemptOutcome&) {
  return 1;
}

inline std::uint64_t CoverPropertySuccessDelta(
    const CoverPropertyAttemptOutcome& outcome) {
  return (!outcome.disabled && outcome.nonvacuous_success) ? 1 : 0;
}

inline std::uint64_t CoverPropertyVacuousSuccessDelta(
    const CoverPropertyAttemptOutcome& outcome) {
  return (!outcome.disabled && outcome.vacuous_success) ? 1 : 0;
}

inline std::uint64_t CoverPropertyPassExecutions(
    const CoverPropertyAttemptOutcome& outcome) {
  if (outcome.disabled) return 0;
  return (outcome.nonvacuous_success || outcome.vacuous_success) ? 1 : 0;
}

inline std::uint64_t CoverSequenceAttemptDelta() { return 1; }

inline bool CoverSequenceMatchCounts(bool disable_iff_occurred) {
  return !disable_iff_occurred;
}

inline std::uint64_t CoverSequenceMatchDelta(
    const std::vector<bool>& completed_match_disable_iff_occurred) {
  std::uint64_t matched = 0;
  for (bool disable_iff_occurred : completed_match_disable_iff_occurred) {
    if (CoverSequenceMatchCounts(disable_iff_occurred)) ++matched;
  }
  return matched;
}

inline std::uint64_t CoverSequencePassExecutions(
    const std::vector<bool>& completed_match_disable_iff_occurred) {
  return CoverSequenceMatchDelta(completed_match_disable_iff_occurred);
}

inline Region CoverPassStatementRegion() { return Region::kReactive; }

}  // namespace delta
