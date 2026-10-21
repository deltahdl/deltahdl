#pragma once

// IEEE 1800-2023 §40.2.2 assertion coverage: whether each assertion has had
// at least one success, with the tallies §40.5.2 reads from an assertion
// handle, and §40.5.3's control of one assertion's coverage through it.

#include <cstdint>
#include <functional>
#include <string>

#include "simulator/coverage_control.h"
#include "simulator/vpi_coverage.h"

namespace delta {

class SimContext;
struct RtlirDesign;
struct Stmt;

// §40.2.2: count the assertions of every instance - those written as its
// module items and those its procedures, tasks and functions hold - as its
// coverable assertions, and collect them. An assertion here is an assert, an
// assume or a cover statement, immediate, deferred or concurrent.
void AttachAssertionCoverage(const RtlirDesign* design, SimContext& ctx);

// §40.5.2: what an attempt of an assertion came to, each a tally the clause
// reads: begun, succeeded nonvacuously (or, for a cover sequence, matched),
// succeeded vacuously, failed, disabled, or killed.
enum class AssertionOutcome : std::uint8_t {
  kAttempt,
  kSuccess,
  kVacuousSuccess,
  kFailure,
  kDisabled,
  kKilled,
};

// §40.2.2 with §40.5.2: `count` outcomes of the assertion `stmt` in the
// instance keyed `prefix`, counted while its coverage is collected; the first
// nonvacuous success covers it. `key` gives the name the assertion API
// keeps the assertion under, asked for once.
void NoteAssertionOutcome(const Stmt* stmt, const std::string& prefix,
                          AssertionOutcome outcome, std::uint64_t count,
                          const std::function<std::string()>& key,
                          CoverageControlState& cov);

// §40.5.2: the tallies of the assertion the API keeps under `key`; zero where
// it has not been attempted.
AssertionCoverageCounters AssertionTallies(const std::string& key,
                                           CoverageControlState& cov);

// §40.5.3: `control` applied to the one assertion kept under `key`, of the
// instance `scope`, with $coverage_control's semantics: a start or a stop
// holds for it until its instance's collection next changes, a reset clears
// its tallies, and each answers whether the instance offers assertion
// coverage, as a check does.
CoverageStatus ControlAssertionCoverage(CoverageControl control,
                                        const std::string& key,
                                        const std::string& scope,
                                        CoverageControlState& cov);

}  // namespace delta
