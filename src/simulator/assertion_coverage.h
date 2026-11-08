#pragma once

#include <cstdint>
#include <functional>
#include <string>

#include "simulator/coverage_control.h"
#include "simulator/vpi_coverage.h"

namespace delta {

class SimContext;
struct RtlirDesign;
struct Stmt;

void AttachAssertionCoverage(const RtlirDesign* design, SimContext& ctx);

enum class AssertionOutcome : std::uint8_t {
  kAttempt,
  kSuccess,
  kVacuousSuccess,
  kFailure,
  kDisabled,
  kKilled,
};

struct AssertionOutcomes {
  AssertionOutcome outcome = AssertionOutcome::kAttempt;
  std::uint64_t count = 1;
};

void NoteAssertionOutcome(const Stmt* stmt, const std::string& prefix,
                          AssertionOutcomes outcomes,
                          const std::function<std::string()>& key,
                          CoverageControlState& cov);

AssertionCoverageCounters AssertionTallies(const std::string& key,
                                           CoverageControlState& cov);

CoverageStatus ControlAssertionCoverage(CoverageControl control,
                                        const std::string& key,
                                        const std::string& scope,
                                        CoverageControlState& cov);

}  // namespace delta
