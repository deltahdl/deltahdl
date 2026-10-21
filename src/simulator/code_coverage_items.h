#pragma once

// The steps each of the four coverage collections (statement_coverage.cpp,
// toggle_coverage.cpp, assertion_coverage.cpp and fsm_coverage.cpp) takes
// over one instance's items of its type, against the run's coverage-control
// state.

#include <cstdint>

#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"

namespace delta {

// §40.3.2.1 and §40.3.2.2: give the instance's `count` items of `type` to its
// scope as the coverable ones, with full availability, and start collecting
// them, as coverage collection starts with the simulation; nothing is covered
// yet.
template <typename Item>
void ArmCoverageInstance(CoverageInstanceItems<Item>& inst, int type,
                         std::int64_t count, CoverageControlState& cov) {
  cov.SetCoverableItems(inst.scope, type, count);
  cov.SetAvailability(inst.scope, type, CoverageAvailability::kFull);
  cov.Control(CoverageControl::kStart, type, inst.scope,
              /*include_below=*/false);
  cov.SetCoveredItems(inst.scope, type, 0);
  inst.resets = cov.ResetCount(inst.scope, type);
}

// §40.3.2.1 `SV_COV_RESET: where the instance's coverage of `type` was reset
// since its items were last looked at, each item is cleared, `clear` saying
// how, and none counts as covered.
template <typename Item, typename Clear>
void ApplyCoverageResets(CoverageInstanceItems<Item>& inst, int type,
                         CoverageControlState& cov, Clear clear) {
  const std::uint64_t kResets = cov.ResetCount(inst.scope, type);
  if (kResets == inst.resets) return;
  inst.resets = kResets;
  for (Item* item : inst.items) clear(*item);
  inst.covered = 0;
}

// §40.3.2.3: one more item of the instance covered, reported as its current
// coverage of `type`.
template <typename Item>
void CountCoveredItem(CoverageInstanceItems<Item>& inst, int type,
                      CoverageControlState& cov) {
  ++inst.covered;
  cov.SetCoveredItems(inst.scope, type, inst.covered);
}

}  // namespace delta
