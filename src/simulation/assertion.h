#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

class Scheduler;
class SimContext;

// =============================================================================
// Assertion result
// =============================================================================

enum class AssertionResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
};

// =============================================================================
// SVA property kind (simple sequence-based properties)
// =============================================================================

enum class SvaPropertyKind : uint8_t {
  kRose,
  kFell,
  kStable,
  kPast,
  kCustom,
};

// =============================================================================
// SvaProperty: a simple SVA property definition
// =============================================================================

struct SvaProperty {
  std::string_view name;
  SvaPropertyKind kind = SvaPropertyKind::kCustom;
  std::string_view signal_name;
  uint32_t past_cycles = 1;
  std::function<bool(uint64_t current, uint64_t previous)> custom_check;
};

// =============================================================================
// AssertionEntry: internal tracking for an active assertion
// =============================================================================

struct AssertionEntry {
  SvaProperty property;
  uint64_t prev_value = 0;
  uint64_t prev_prev_value = 0;
  uint32_t cycle_count = 0;
  AssertionResult last_result = AssertionResult::kVacuousPass;
};

// =============================================================================
// AssertionMonitor: evaluates properties each clock cycle
// =============================================================================

class AssertionMonitor {
 public:
  void AddProperty(SvaProperty prop);
  void Attach(SimContext& ctx, Scheduler& sched);
  AssertionResult Evaluate(std::string_view prop_name, uint64_t current_val);
  void Tick(SimContext& ctx);
  uint32_t PropertyCount() const {
    return static_cast<uint32_t>(entries_.size());
  }
  uint32_t FailCount() const { return fail_count_; }
  uint32_t PassCount() const { return pass_count_; }
  const AssertionEntry* FindEntry(std::string_view name) const;

 private:
  AssertionResult EvaluateEntry(AssertionEntry& entry, uint64_t current_val);

  std::vector<AssertionEntry> entries_;
  uint32_t fail_count_ = 0;
  uint32_t pass_count_ = 0;
};

}  // namespace delta
