#pragma once

#include <cstdint>

#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"

namespace delta {

template <typename Item>
void ArmCoverageInstance(CoverageInstanceItems<Item>& inst, int type,
                         std::int64_t count, CoverageControlState& cov) {
  cov.SetCoverableItems(inst.scope, type, count);
  cov.SetAvailability(inst.scope, type, CoverageAvailability::kFull);
  cov.Control(CoverageControl::kStart, type, inst.scope, false);
  cov.SetCoveredItems(inst.scope, type, 0);
  inst.resets = cov.ResetCount(inst.scope, type);
}

template <typename Item, typename Clear>
void ApplyCoverageResets(CoverageInstanceItems<Item>& inst, int type,
                         CoverageControlState& cov, Clear clear) {
  const std::uint64_t kResets = cov.ResetCount(inst.scope, type);
  if (kResets == inst.resets) return;
  inst.resets = kResets;
  for (Item* item : inst.items) clear(*item);
  inst.covered = 0;
}

template <typename Item>
void CountCoveredItem(CoverageInstanceItems<Item>& inst, int type,
                      CoverageControlState& cov) {
  ++inst.covered;
  cov.SetCoveredItems(inst.scope, type, inst.covered);
}

}  // namespace delta
