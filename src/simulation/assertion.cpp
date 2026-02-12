#include "simulation/assertion.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

namespace delta {

// =============================================================================
// AssertionMonitor
// =============================================================================

void AssertionMonitor::AddProperty(SvaProperty prop) {
  AssertionEntry entry;
  entry.property = std::move(prop);
  entries_.push_back(std::move(entry));
}

static void RegisterAssertionWatcher(AssertionMonitor* monitor, Variable* var,
                                     const std::string& prop_name,
                                     Scheduler& sched) {
  var->AddWatcher([monitor, var, prop_name, &sched]() {
    auto* ev = sched.GetEventPool().Acquire();
    uint64_t val = var->value.ToUint64();
    ev->callback = [monitor, prop_name, val]() {
      monitor->Evaluate(prop_name, val);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kObserved, ev);
    RegisterAssertionWatcher(monitor, var, prop_name, sched);
    return true;
  });
}

void AssertionMonitor::Attach(SimContext& ctx, Scheduler& sched) {
  for (auto& entry : entries_) {
    auto* var = ctx.FindVariable(entry.property.signal_name);
    if (!var) continue;
    std::string prop_name(entry.property.name);
    RegisterAssertionWatcher(this, var, prop_name, sched);
  }
  sched.SetPostTimestepCallback([this, &ctx]() { Tick(ctx); });
}

AssertionResult AssertionMonitor::Evaluate(std::string_view prop_name,
                                           uint64_t current_val) {
  for (auto& entry : entries_) {
    if (entry.property.name != prop_name) continue;
    auto result = EvaluateEntry(entry, current_val);
    entry.last_result = result;
    if (result == AssertionResult::kPass) {
      ++pass_count_;
    } else if (result == AssertionResult::kFail) {
      ++fail_count_;
    }
    return result;
  }
  return AssertionResult::kVacuousPass;
}

void AssertionMonitor::Tick(SimContext& /*ctx*/) {
  for (auto& entry : entries_) {
    ++entry.cycle_count;
  }
}

const AssertionEntry* AssertionMonitor::FindEntry(std::string_view name) const {
  for (const auto& entry : entries_) {
    if (entry.property.name == name) return &entry;
  }
  return nullptr;
}

AssertionResult AssertionMonitor::EvaluateEntry(AssertionEntry& entry,
                                                uint64_t current_val) {
  if (entry.cycle_count == 0) {
    entry.prev_prev_value = entry.prev_value;
    entry.prev_value = current_val;
    return AssertionResult::kVacuousPass;
  }

  AssertionResult result = AssertionResult::kVacuousPass;
  uint64_t prev = entry.prev_value;

  switch (entry.property.kind) {
    case SvaPropertyKind::kRose:
      // $rose: signal was 0 and is now 1 (bit 0).
      result = (prev & 1) == 0 && (current_val & 1) == 1
                   ? AssertionResult::kPass
                   : AssertionResult::kFail;
      break;
    case SvaPropertyKind::kFell:
      // $fell: signal was 1 and is now 0 (bit 0).
      result = (prev & 1) == 1 && (current_val & 1) == 0
                   ? AssertionResult::kPass
                   : AssertionResult::kFail;
      break;
    case SvaPropertyKind::kStable:
      // $stable: signal did not change.
      result =
          current_val == prev ? AssertionResult::kPass : AssertionResult::kFail;
      break;
    case SvaPropertyKind::kPast:
      // $past: always passes (value is available via prev_value).
      result = AssertionResult::kPass;
      break;
    case SvaPropertyKind::kCustom:
      if (entry.property.custom_check) {
        result = entry.property.custom_check(current_val, prev)
                     ? AssertionResult::kPass
                     : AssertionResult::kFail;
      }
      break;
  }

  entry.prev_prev_value = prev;
  entry.prev_value = current_val;
  return result;
}

}  // namespace delta
