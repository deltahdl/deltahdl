#include "simulator/sva_engine.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/scheduler.h"

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
// §16.2 — assertion kinds
// =============================================================================

bool IsImmediateAssertionKindAllowed(AssertionKind kind) {
  // §16.2: "There is no immediate restrict assertion statement."
  return kind != AssertionKind::kRestrict;
}

bool ConcurrentTimingUsesSampledValues(AssertionTiming timing) {
  // §16.2: "Concurrent assertions are based on clock semantics and use
  // sampled values of their expressions."  Immediate assertions are
  // executed under simulation event semantics and do not.
  return timing == AssertionTiming::kConcurrent;
}

// =============================================================================
// §16.5.1 — sampled values
// =============================================================================

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default) {
  // §16.5.1: "The sampled value of a variable in a time slot corresponding
  // to time greater than 0 is the value of this variable in the Preponed
  // region of this time slot."  At time 0 the default sampled value is
  // used.
  if (t.ticks == 0) {
    return SampledValue{type_default, SampleMode::kDefault};
  }
  return SampledValue{preponed_value, SampleMode::kPreponed};
}

SampledValue SampleAutomaticVariable(uint64_t current_value) {
  // §16.5.1: "Sampled values of automatic variables (see 16.14.6), local
  // variables (see 16.10), and active free checker variables are their
  // current values."
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue DefaultSampledValueOfTriggered() {
  // §16.5.1: "The default sampled value of the `triggered` event method
  // ... is false (1'b0)."
  return SampledValue{0, SampleMode::kDefault};
}

SampledValue DefaultSampledValueOfMatched() {
  // §16.5.1: the sequence methods `triggered` and `matched` share the
  // same false default sampled value.
  return SampledValue{0, SampleMode::kDefault};
}

SampledValue SampleSingleVariableExpression(SampledValue var_sample) {
  // §16.5.1: "The sampled value of an expression consisting of a single
  // variable is the sampled value of this variable."  The expression
  // sampled value is the variable's sampled value, unchanged.
  return var_sample;
}

SampledValue SampleConstCastExpression(uint64_t argument_current_value) {
  // §16.5.1: "The sampled value of a `const` cast expression ... is
  // defined as the current value of its argument."
  return SampledValue{argument_current_value, SampleMode::kCurrent};
}

SampledValue SampledValueOfTriggered(bool current_returned) {
  // §16.5.1: "The sampled value of the `triggered` event method ... is
  // defined as the current value returned by the event property or
  // sequence method."
  return SampledValue{current_returned ? 1u : 0u, SampleMode::kCurrent};
}

SampledValue SampledValueOfMatched(bool current_returned) {
  // §16.5.1: same rule for the sequence method `matched`.
  return SampledValue{current_returned ? 1u : 0u, SampleMode::kCurrent};
}

SampledValue SampleRecursiveExpression(
    SampledValue a, SampledValue b,
    uint64_t (*combinator)(uint64_t, uint64_t)) {
  // §16.5.1: "The sampled value of any other expression is defined
  // recursively using the values of its arguments."  The combinator is
  // applied to the already-sampled subexpressions.  The composite mode
  // tracks kCurrent if either side is current (since current-value
  // semantics propagate per the §16.14.6 exception), otherwise stays
  // Preponed.
  SampleMode mode =
      (a.mode == SampleMode::kCurrent || b.mode == SampleMode::kCurrent)
          ? SampleMode::kCurrent
          : SampleMode::kPreponed;
  return SampledValue{combinator(a.value, b.value), mode};
}

SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default) {
  // §16.5.1: "The default sampled value of any other variable or net is
  // the default value of the corresponding type."
  return SampledValue{type_default, SampleMode::kDefault};
}

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew) {
  // §16.5.1: "If a variable is an input variable of a clocking block,
  // the variable shall be sampled by the clocking block with #1step
  // sampling.  Any other type of sampling for the clocking block
  // variable shall result in an error."
  return skew == ClockingInputSkew::kStep1;
}

// =============================================================================
// §16.14.6 — procedural assertion queue
// =============================================================================

void ProceduralAssertionQueue::Enqueue(PendingProceduralAssertion pending) {
  // §16.14.6: incoming entries are pending; they are not yet matured.
  pending.matured = false;
  queue_.push_back(std::move(pending));
}

void ProceduralAssertionQueue::MatureAll() {
  // §16.14.6: "In the Observed region of each simulation time step, each
  // pending procedural assertion instance that is currently present in a
  // procedural assertion queue shall mature, which means it is confirmed
  // for execution."
  for (auto& p : queue_) p.matured = true;
}

void ProceduralAssertionQueue::Flush() {
  // §16.14.6: "If a procedural assertion flush point ... is reached in a
  // process, its procedural assertion queue is cleared.  Any currently
  // pending procedural assertion instances will not mature, unless again
  // placed on the queue."
  queue_.clear();
}

uint32_t ProceduralAssertionQueue::Size() const {
  return static_cast<uint32_t>(queue_.size());
}

uint32_t ProceduralAssertionQueue::MaturedCount() const {
  uint32_t n = 0;
  for (const auto& p : queue_) {
    if (p.matured) ++n;
  }
  return n;
}

bool IsStaticConcurrentAssertion(bool appears_in_procedural_code) {
  // §16.14.6: "A concurrent assertion statement that appears outside
  // procedural code is referred to as a static concurrent assertion
  // statement."  The negation of the procedural-context flag.
  return !appears_in_procedural_code;
}

bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic) {
  // §16.14.6: "It shall be illegal to use automatic variables in
  // clocking events."
  return !variable_is_automatic;
}

InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock,
    std::string_view default_clock) {
  // §16.14.6: "If no clocking event is specified in a procedural
  // concurrent assertion, the leading clocking event of the assertion
  // shall be inferred from the procedural context, if possible.  If no
  // clock can be inferred from the procedural context, then the clocks
  // shall be inferred from the default clocking ..."
  if (!proc_context_clock.empty()) {
    return InferredClock{InferredClockKind::kFromProceduralContext,
                         proc_context_clock};
  }
  if (!default_clock.empty()) {
    return InferredClock{InferredClockKind::kFromDefaultClocking,
                         default_clock};
  }
  return InferredClock{InferredClockKind::kNotInferrable, {}};
}

bool SatisfiesClockInferenceRequirements(bool no_blocking_timing_control,
                                          bool exactly_one_event_control,
                                          bool unique_qualifying_event_expr) {
  // §16.14.6: "A clock shall be inferred for the context of an always
  // or initial procedure that satisfies the following requirements:"
  // a) no blocking timing control, b) exactly one event control,
  // c) exactly one qualifying event expression.  All three must hold.
  return no_blocking_timing_control && exactly_one_event_control &&
         unique_qualifying_event_expr;
}

void MaturedAssertionQueue::Place(PendingProceduralAssertion matured) {
  // §16.14.6: matured instances whose leading clocking event has not
  // occurred this time step go to the matured queue to wait for the
  // next clocking event.
  matured.matured = true;
  queue_.push_back(std::move(matured));
}

std::vector<PendingProceduralAssertion> MaturedAssertionQueue::TakeAll() {
  return std::exchange(queue_, {});
}

uint32_t MaturedAssertionQueue::Size() const {
  return static_cast<uint32_t>(queue_.size());
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

ProceduralAssertionQueue& SvaEngine::GetProceduralQueue(
    std::string_view process_id) {
  // §16.14.6: lazily allocate a procedural assertion queue per executing
  // process.  Each process owns its own queue.
  return procedural_queues_[std::string(process_id)];
}

}  // namespace delta
