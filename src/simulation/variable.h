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

  std::vector<std::function<void()>> watchers;

  void AddWatcher(std::function<void()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    auto pending = std::move(watchers);
    watchers.clear();
    for (auto& cb : pending) {
      cb();
    }
  }
};

}  // namespace delta
