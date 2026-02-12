#pragma once

#include <cstdint>
#include <functional>
#include <vector>

#include "common/types.h"

namespace delta {

// --- Variable: storage for reg/logic/integer simulation objects ---

struct Variable {
  Logic4Vec value{};
  Logic4Vec prev_value{};
  bool is_forced = false;
  Logic4Vec forced_value{};
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
  bool is_event = false;
  bool is_signed = false;

  // Watchers return true if consumed (should be removed), false to keep.
  std::vector<std::function<bool()>> watchers;

  void AddWatcher(std::function<bool()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    auto pending = std::move(watchers);
    for (auto& cb : pending) {
      if (!cb()) watchers.push_back(std::move(cb));
    }
  }
};

}  // namespace delta
