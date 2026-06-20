#pragma once

#include <cstdint>
#include <functional>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;

struct Variable {
  Logic4Vec value{};
  Logic4Vec prev_value{};
  bool is_forced = false;
  Logic4Vec forced_value{};
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
  bool is_event = false;
  bool is_null_event = false;
  bool is_signed = false;
  bool is_4state = true;
  uint64_t triggered_ticks = UINT64_MAX;

  const Expr* proc_cont_rhs = nullptr;

  const Expr* assign_cont_rhs = nullptr;

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
