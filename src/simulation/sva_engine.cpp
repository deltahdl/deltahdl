#include "simulation/sva_engine.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulation/scheduler.h"

namespace delta {

// =============================================================================
// Assertion severity
// =============================================================================

std::string_view SeverityToString(AssertionSeverity sev) {
  switch (sev) {
    case AssertionSeverity::kInfo:
      return "INFO";
    case AssertionSeverity::kWarning:
      return "WARNING";
    case AssertionSeverity::kError:
      return "ERROR";
    case AssertionSeverity::kFatal:
      return "FATAL";
  }
  return "ERROR";
}

// =============================================================================
// SequenceAttempt
// =============================================================================

void AdvanceSequence(SequenceAttempt& sa) {
  if (sa.delay_remaining > 0) {
    --sa.delay_remaining;
  }
}

// =============================================================================
// Sequence matching: consecutive repetition [*N] / [*M:N]
// =============================================================================

bool MatchRepetition(const SvaSequence& seq,
                     const std::vector<uint64_t>& vals) {
  uint32_t consecutive = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++consecutive;
    } else {
      break;
    }
  }
  return consecutive >= seq.rep_min && consecutive <= seq.rep_max;
}

// =============================================================================
// Sequence matching: goto repetition [->N]
// =============================================================================

bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals) {
  if (vals.empty()) return seq.rep_min == 0;
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }
  // Goto: last element must be a match.
  bool last_matches = seq.expr_check && seq.expr_check(vals.back());
  return last_matches && match_count >= seq.rep_min &&
         match_count <= seq.rep_max;
}

// =============================================================================
// Sequence matching: non-consecutive repetition [=N]
// =============================================================================

bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals) {
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }
  return match_count >= seq.rep_min && match_count <= seq.rep_max;
}

// =============================================================================
// Sequence matching: delay ##N
// =============================================================================

bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals) {
  if (vals.size() <= seq.delay_cycles) return false;
  uint64_t check_val = vals[seq.delay_cycles];
  return seq.expr_check && seq.expr_check(check_val);
}

// =============================================================================
// Sequence operators
// =============================================================================

bool EvalSequenceAnd(bool a_match, bool b_match) { return a_match && b_match; }

bool EvalSequenceOr(bool a_match, bool b_match) { return a_match || b_match; }

bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len) {
  return a_match && b_match && a_len == b_len;
}

bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values) {
  return std::all_of(values.begin(), values.end(), check);
}

// =============================================================================
// Property evaluation
// =============================================================================

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping) {
  if (!antecedent) return PropertyResult::kVacuousPass;
  if (non_overlapping) return PropertyResult::kPending;
  return consequent ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalPropertyNot(PropertyResult inner) {
  if (inner == PropertyResult::kPass || inner == PropertyResult::kVacuousPass) {
    return PropertyResult::kFail;
  }
  return PropertyResult::kPass;
}

PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b) {
  if (a == PropertyResult::kFail || b == PropertyResult::kFail) {
    return PropertyResult::kFail;
  }
  return PropertyResult::kPass;
}

PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b) {
  if (a == PropertyResult::kPass || a == PropertyResult::kVacuousPass) {
    return PropertyResult::kPass;
  }
  if (b == PropertyResult::kPass || b == PropertyResult::kVacuousPass) {
    return PropertyResult::kPass;
  }
  return PropertyResult::kFail;
}

PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner) {
  if (disable_cond) return PropertyResult::kVacuousPass;
  return inner;
}

PropertyResult ResolveNonOverlapping(bool consequent_matched) {
  return consequent_matched ? PropertyResult::kPass : PropertyResult::kFail;
}

// =============================================================================
// DeferredAssertion action execution
// =============================================================================

void ExecuteDeferredAssertionAction(const DeferredAssertion& da) {
  if (da.condition_val != 0) {
    if (da.pass_action) da.pass_action();
  } else {
    if (da.fail_action) da.fail_action();
  }
}

// =============================================================================
// AssertionControl
// =============================================================================

bool AssertionControl::IsEnabled(std::string_view inst) const {
  if (global_off_) return false;
  return disabled_.find(std::string(inst)) == disabled_.end() &&
         killed_.find(std::string(inst)) == killed_.end();
}

void AssertionControl::SetOff(std::string_view inst) {
  disabled_.insert(std::string(inst));
}

void AssertionControl::SetOn(std::string_view inst) {
  disabled_.erase(std::string(inst));
}

void AssertionControl::Kill(std::string_view inst) {
  killed_.insert(std::string(inst));
  disabled_.insert(std::string(inst));
}

bool AssertionControl::WasKilled(std::string_view inst) const {
  return killed_.find(std::string(inst)) != killed_.end();
}

void AssertionControl::SetGlobalOff() { global_off_ = true; }

void AssertionControl::SetGlobalOn() { global_off_ = false; }

bool AssertionControl::IsPassEnabled(std::string_view inst) const {
  return pass_off_.find(std::string(inst)) == pass_off_.end();
}

void AssertionControl::SetPassOff(std::string_view inst) {
  pass_off_.insert(std::string(inst));
}

bool AssertionControl::IsFailEnabled(std::string_view inst) const {
  return fail_off_.find(std::string(inst)) == fail_off_.end();
}

void AssertionControl::SetFailOff(std::string_view inst) {
  fail_off_.insert(std::string(inst));
}

void AssertionControl::SetFailOn(std::string_view inst) {
  fail_off_.erase(std::string(inst));
}

// =============================================================================
// SvaEngine
// =============================================================================

void SvaEngine::QueueDeferredAssertion(const DeferredAssertion& da) {
  deferred_queue_.push_back(da);
}

void SvaEngine::QueueDeferredAssertionIfEnabled(const DeferredAssertion& da) {
  if (!control_.IsEnabled(da.instance_name)) return;
  deferred_queue_.push_back(da);
}

void SvaEngine::FlushDeferredAssertions(Scheduler& sched, SimTime time) {
  auto queue = std::move(deferred_queue_);
  deferred_queue_.clear();
  for (auto& da : queue) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kObserved, event);
  }
}

void SvaEngine::FlushDeferredAssertionsRespectingControl(Scheduler& sched,
                                                         SimTime time) {
  auto queue = std::move(deferred_queue_);
  deferred_queue_.clear();
  for (auto& da : queue) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [this, da_copy = std::move(da)]() {
      bool is_pass = (da_copy.condition_val != 0);
      if (is_pass && !control_.IsPassEnabled(da_copy.instance_name)) return;
      if (!is_pass && !control_.IsFailEnabled(da_copy.instance_name)) return;
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kObserved, event);
  }
}

void SvaEngine::KillAssertionsForInstance(std::string_view inst) {
  control_.Kill(inst);
  std::string inst_str(inst);
  std::erase_if(deferred_queue_, [&inst_str](const DeferredAssertion& da) {
    return da.instance_name == inst_str;
  });
}

uint32_t SvaEngine::DeferredQueueSize() const {
  return static_cast<uint32_t>(deferred_queue_.size());
}

}  // namespace delta
