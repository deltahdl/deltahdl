#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"

namespace delta {

class Scheduler;

// =============================================================================
// Assertion severity (section 16.3)
// =============================================================================

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

std::string_view SeverityToString(AssertionSeverity sev);

// =============================================================================
// Property evaluation result
// =============================================================================

enum class PropertyResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
  kPending,  // For non-overlapping implication awaiting next cycle.
};

// =============================================================================
// SequenceAttempt: tracks in-progress sequence match (section 16.9)
// =============================================================================

struct SequenceAttempt {
  uint32_t position = 0;
  uint32_t delay_remaining = 0;
  uint32_t match_count = 0;
  bool completed = false;
  bool failed = false;
};

void AdvanceSequence(SequenceAttempt& sa);

// =============================================================================
// SvaSequence: describes a sequence pattern
// =============================================================================

enum class SvaSequenceKind : uint8_t {
  kDelay,
  kConsecutiveRepetition,
  kGotoRepetition,
  kNonConsecutiveRepetition,
};

struct SvaSequence {
  SvaSequenceKind kind = SvaSequenceKind::kDelay;
  uint32_t delay_cycles = 0;
  uint32_t rep_min = 0;
  uint32_t rep_max = 0;
  std::function<bool(uint64_t)> expr_check;
};

// Sequence matching functions.
bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

// =============================================================================
// Sequence operators (section 16.9.6-9)
// =============================================================================

bool EvalSequenceAnd(bool a_match, bool b_match);
bool EvalSequenceOr(bool a_match, bool b_match);
bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

// =============================================================================
// Property evaluation (section 16.12)
// =============================================================================

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping);
PropertyResult EvalPropertyNot(PropertyResult inner);
PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);
PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);
PropertyResult ResolveNonOverlapping(bool consequent_matched);

// =============================================================================
// DeferredAssertion: queued for Observed region (section 16.4)
// =============================================================================

struct DeferredAssertion {
  uint64_t condition_val = 0;
  std::string instance_name;
  std::function<void()> pass_action;
  std::function<void()> fail_action;
  AssertionSeverity severity = AssertionSeverity::kError;
};

void ExecuteDeferredAssertionAction(const DeferredAssertion& da);

// =============================================================================
// AssertionControl: per-instance assertion control (section 16.13)
// =============================================================================

class AssertionControl {
 public:
  bool IsEnabled(std::string_view inst) const;
  void SetOff(std::string_view inst);
  void SetOn(std::string_view inst);
  void Kill(std::string_view inst);
  bool WasKilled(std::string_view inst) const;

  void SetGlobalOff();
  void SetGlobalOn();

  bool IsPassEnabled(std::string_view inst) const;
  void SetPassOff(std::string_view inst);

  bool IsFailEnabled(std::string_view inst) const;
  void SetFailOff(std::string_view inst);
  void SetFailOn(std::string_view inst);

 private:
  bool global_off_ = false;
  std::unordered_set<std::string> disabled_;
  std::unordered_set<std::string> killed_;
  std::unordered_set<std::string> pass_off_;
  std::unordered_set<std::string> fail_off_;
};

// =============================================================================
// SvaEngine: top-level SVA engine (section 16)
// =============================================================================

class SvaEngine {
 public:
  void QueueDeferredAssertion(const DeferredAssertion& da);
  void QueueDeferredAssertionIfEnabled(const DeferredAssertion& da);
  void FlushDeferredAssertions(Scheduler& sched, SimTime time);
  void FlushDeferredAssertionsRespectingControl(Scheduler& sched, SimTime time);
  void KillAssertionsForInstance(std::string_view inst);

  uint32_t DeferredQueueSize() const;
  AssertionControl& GetControl() { return control_; }

 private:
  std::vector<DeferredAssertion> deferred_queue_;
  AssertionControl control_;
};

}  // namespace delta
