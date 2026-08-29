#pragma once

#include <cstdint>
#include <functional>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"

namespace delta {

struct Expr;

struct Variable {
  Logic4Vec value{};
  Logic4Vec prev_value{};

  // §30.5.3: the simulation time this variable's value last changed, in ticks.
  // "Active specify paths are those whose input has transitioned most recently
  // in time", and choosing among the module paths reaching one output is the
  // only thing that asks. Nothing writes it but the watcher
  // WatchModulePathSources in src/simulator/module_path_delay.cpp arms, and
  // that arms only on the source terminal of a registered module path, so it
  // stays 0 for every other variable in the design and for every design that
  // declared no specify block. Zero therefore means "never recorded", not
  // "changed at time zero", and only paths watched by the same arming are ever
  // compared against each other.
  uint64_t last_change_ticks = 0;

  bool is_forced = false;
  Logic4Vec forced_value{};
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
  bool is_event = false;
  bool is_null_event = false;
  bool is_signed = false;
  bool is_4state = true;
  uint64_t triggered_ticks = UINT64_MAX;

  // §7.4.1: for a packed multidimensional array stored as one flat vector (e.g.
  // `logic [1:0][7:0]`), the bit width of one outermost element. A single-index
  // select `x[i]` then selects that many bits at the element's offset instead
  // of one bit. Zero means an ordinary vector (single-bit selects).
  uint32_t packed_elem_width = 0;

  // §11.5.1: the outermost packed dimension of this variable's declaration,
  // exactly as written, recorded only when the declaration carries one. An
  // `int`, a scalar and a string carry none and are addressed as [width-1:0].
  // For a packed multidimensional array the range indexes elements rather than
  // bits, matching packed_elem_width above.
  bool has_packed_range = false;
  PackedRange packed_range{};

  // The range an index in a select of this variable is resolved against.
  PackedRange DeclaredRange() const {
    return has_packed_range ? packed_range : PackedRange::Implicit(value.width);
  }

  // The range a select addressed by bit resolves against. A packed
  // multidimensional array's declared outer range counts elements rather than
  // bits (§7.4.1), so a select that addresses this variable's bits keeps the
  // flattened [width-1:0] view of it.
  PackedRange BitSelectRange() const {
    if (packed_elem_width > 1) return PackedRange::Implicit(value.width);
    return DeclaredRange();
  }

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
