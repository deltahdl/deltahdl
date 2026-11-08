#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"

namespace delta {

struct DataType;

struct Expr;
struct StructTypeInfo;
struct ToggleSignal;

void ObserveToggle(ToggleSignal& signal);

struct ProcContAssignWindow {
  uint32_t rhs_width = 0;
  uint32_t src_lo = 0;
  uint32_t src_width = 0;
  uint32_t dst_lo = 0;
  uint32_t dst_width = 0;
};

struct PackedLevel {
  PackedRange range;
  uint32_t elem_width = 1;

  uint64_t Width() const {
    return static_cast<uint64_t>(range.HighIndex() - range.LowIndex() + 1) *
           elem_width;
  }
};

struct Variable {
  Logic4Vec value{};
  Logic4Snapshot prev_value{};

  bool is_string = false;

  bool is_real = false;

  bool is_virtual_interface = false;

  const StructTypeInfo* local_layout = nullptr;

  uint64_t last_change_ticks = 0;
  std::vector<uint64_t> bit_change_ticks;
  static constexpr uint8_t kEdgeRise = 1;
  static constexpr uint8_t kEdgeFall = 2;
  uint8_t last_change_edge = 0;
  std::vector<uint8_t> bit_change_edges;

  bool is_forced = false;
  bool force_active = false;
  Logic4Vec forced_value{};
  struct HeldPart {
    ProcContAssignWindow window;
    const Expr* rhs = nullptr;
  };
  std::vector<HeldPart> held_parts;
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
  bool is_event = false;
  bool is_null_event = false;
  bool is_signed = false;
  bool is_4state = true;
  uint64_t triggered_ticks = UINT64_MAX;
  uint64_t strength_generation = 0;

  const DataType* declared_type = nullptr;
  std::string_view declared_scope;
  std::string_view declared_unpacked;

  uint32_t packed_elem_width = 0;

  bool has_packed_range = false;
  PackedRange packed_range{};

  std::vector<PackedRange> inner_packed_dims;

  std::optional<size_t> signed_elem_depth;

  PackedRange DeclaredRange() const {
    return has_packed_range ? packed_range : PackedRange::Implicit(value.width);
  }

  std::optional<PackedLevel> PackedLevelAt(size_t depth) const {
    if (depth == 0) {
      return PackedLevel{DeclaredRange(),
                         std::max<uint32_t>(packed_elem_width, 1)};
    }
    if (depth > inner_packed_dims.size()) return std::nullopt;
    PackedLevel level{inner_packed_dims[depth - 1], 1};
    for (size_t i = depth; i < inner_packed_dims.size(); ++i) {
      level.elem_width *=
          static_cast<uint32_t>(inner_packed_dims[i].HighIndex() -
                                inner_packed_dims[i].LowIndex() + 1);
    }
    return level;
  }

  std::optional<PackedLevel> PackedLevelWithin(size_t depth,
                                               uint32_t width) const {
    auto level = PackedLevelAt(depth);
    if (level && depth > 0 && level->Width() != width) return std::nullopt;
    return level;
  }

  PackedRange BitSelectRange() const {
    if (packed_elem_width > 1) return PackedRange::Implicit(value.width);
    return DeclaredRange();
  }

  bool BitIsForced(uint32_t bit) const {
    if (!is_forced) return false;
    return std::ranges::any_of(held_parts, [bit](const HeldPart& part) {
      return part.window.dst_width == 0 ||
             (bit >= part.window.dst_lo &&
              bit < part.window.dst_lo + part.window.dst_width);
    });
  }

  bool WholeIsForced() const {
    if (!is_forced) return false;
    if (held_parts.empty()) return true;
    return std::ranges::any_of(held_parts, [this](const HeldPart& part) {
      return part.window.dst_width == 0 ||
             (part.window.dst_lo == 0 && part.window.dst_width == value.width);
    });
  }

  const Expr* proc_cont_rhs = nullptr;

  const Expr* assign_cont_rhs = nullptr;

  ProcContAssignWindow assign_cont_window{};

  std::function<void()> cont_assign_reevaluate;

  std::vector<std::function<bool()>> watchers;
  ToggleSignal* toggle = nullptr;

  void AddWatcher(std::function<bool()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    if (toggle != nullptr) ObserveToggle(*toggle);
    auto pending = std::move(watchers);
    for (auto& cb : pending) {
      if (!cb()) watchers.push_back(std::move(cb));
    }
  }
};

}  // namespace delta
