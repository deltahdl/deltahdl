#include "simulator/sva_engine_sampling.h"

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/sim_context_types.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

namespace delta {

SequencePropertyStrength DefaultSequencePropertyStrength(AssertionKind stmt) {
  if (stmt == AssertionKind::kAssert || stmt == AssertionKind::kAssume) {
    return SequencePropertyStrength::kWeak;
  }
  return SequencePropertyStrength::kStrong;
}

PropertyResult EvalStrongSequenceProperty(bool has_nonempty_match) {
  return has_nonempty_match ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalWeakSequenceProperty(
    bool finite_prefix_witnesses_inability) {
  return finite_prefix_witnesses_inability ? PropertyResult::kFail
                                           : PropertyResult::kPass;
}

SequencePropertyStrength NegatePropertyStrength(
    SequencePropertyStrength inner) {
  return inner == SequencePropertyStrength::kWeak
             ? SequencePropertyStrength::kStrong
             : SequencePropertyStrength::kWeak;
}

bool IsImmediateAssertionKindAllowed(AssertionKind kind) {
  return kind != AssertionKind::kRestrict;
}

bool ConcurrentTimingUsesSampledValues(AssertionTiming timing) {
  return timing == AssertionTiming::kConcurrent;
}

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default) {
  if (t.ticks == 0) {
    return SampledValue{type_default, SampleMode::kDefault};
  }
  return SampledValue{preponed_value, SampleMode::kPreponed};
}

SampledValue SampleAutomaticVariable(uint64_t current_value) {
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue SampleLocalVariable(uint64_t current_value) {
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue SampleActiveFreeCheckerVariable(uint64_t current_value) {
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue SampleActiveFreeCheckerVarPastFuture(uint64_t postponed_value) {
  return SampledValue{postponed_value, SampleMode::kPostponed};
}

SampledValue SampleAutomaticVarPastFuture(uint64_t current_value) {
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue DefaultSampledValueOfTriggered() {
  return SampledValue{0, SampleMode::kDefault};
}

SampledValue DefaultSampledValueOfMatched() {
  return SampledValue{0, SampleMode::kDefault};
}

SampledValue SampleSingleVariableExpression(SampledValue var_sample) {
  return var_sample;
}

SampledValue SampleConstCastExpression(uint64_t argument_current_value) {
  return SampledValue{argument_current_value, SampleMode::kCurrent};
}

SampledValue SampleProceduralAssertionArgument(uint64_t current_value) {
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue ProceduralArgumentValueAfterMature(SampledValue captured,
                                                uint64_t) {
  return captured;
}

bool ProceduralExecutionAffects(ProceduralExecutionEffect effect,
                                bool already_matured) {
  if (!already_matured) return true;
  return effect == ProceduralExecutionEffect::kActivation;
}

SampledValue SampleProceduralAssertionActionBlockArgument(
    uint64_t current_value) {
  return SampleProceduralAssertionArgument(current_value);
}

bool ActionBlockMayModifyArgument() { return false; }

uint64_t ReadProceduralConditionalGuard(uint64_t current_value, uint64_t) {
  return current_value;
}

SampledValue SampledValueOfTriggered(bool current_returned) {
  return SampledValue{current_returned ? 1u : 0u, SampleMode::kCurrent};
}

SampledValue SampledValueOfMatched(bool current_returned) {
  return SampledValue{current_returned ? 1u : 0u, SampleMode::kCurrent};
}

SampledValue SampleRecursiveExpression(SampledValue a, SampledValue b,
                                       uint64_t (*combinator)(uint64_t,
                                                              uint64_t)) {
  SampleMode mode =
      (a.mode == SampleMode::kCurrent || b.mode == SampleMode::kCurrent)
          ? SampleMode::kCurrent
          : SampleMode::kPreponed;
  return SampledValue{combinator(a.value, b.value), mode};
}

SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default) {
  return SampledValue{type_default, SampleMode::kDefault};
}

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew) {
  return skew == ClockingInputSkew::kStep1;
}

bool InterpretAssertionExprAsBoolean(uint64_t aval, uint64_t bval) {
  if (bval != 0) return false;
  return aval != 0;
}

SampledArrayElement SampleArrayElementForAssertion(uint64_t element_value) {
  return SampledArrayElement{element_value, true};
}

SampledArrayElement ArrayElementAfterArrayMutation(
    SampledArrayElement sampled) {
  return sampled;
}

bool SampledArrayElementStillReadable(const SampledArrayElement& sampled) {
  return sampled.live;
}

bool BooleanExprUsesSampledValues(BooleanExprPlace place) {
  switch (place) {
    case BooleanExprPlace::kSequenceOrPropertyExpr:
      return true;
    case BooleanExprPlace::kClockingEvent:
    case BooleanExprPlace::kDisableCondition:
      return false;
  }
  return false;
}

bool DisableConditionUsesCurrentValues() { return true; }

bool DisableConditionAllowsTriggeredMethod() { return true; }

bool DisableConditionAllowsMatchedMethod() { return false; }

bool DisableConditionAllowsLocalVariableReference() { return false; }

static void CopySample(const Logic4Vec& src, Logic4Vec& dst, Arena& arena) {
  if (dst.words == nullptr || dst.width != src.width) {
    dst = MakeLogic4Vec(arena, src.width);
  }
  dst.is_real = src.is_real;
  dst.is_signed = src.is_signed;
  dst.is_string = src.is_string;
  for (uint32_t i = 0; i < dst.nwords && i < src.nwords; ++i) {
    dst.words[i] = src.words[i];
  }
}

void AssertionSampleStore::Register(const Variable* var, Arena& arena) {
  if (var == nullptr || entries_.count(var) != 0 || excluded_.count(var) != 0)
    return;
  Entry entry;
  CopySample(var->value, entry.default_value, arena);
  CopySample(var->value, entry.preponed_value, arena);
  entries_.emplace(var, entry);
}

static void CopyQueueSample(const std::vector<Logic4Vec>& src,
                            std::vector<Logic4Vec>& dst, Arena& arena) {
  dst.resize(src.size());
  for (size_t i = 0; i < src.size(); ++i) CopySample(src[i], dst[i], arena);
}

void AssertionSampleStore::RegisterQueue(const QueueObject* queue,
                                         Arena& arena) {
  if (queue == nullptr || queue_entries_.count(queue) != 0) return;
  QueueEntry entry;
  CopyQueueSample(queue->elements, entry.default_elements, arena);
  CopyQueueSample(queue->elements, entry.preponed_elements, arena);
  queue_entries_.emplace(queue, std::move(entry));
}

void AssertionSampleStore::Refill(Arena& arena) {
  for (auto& [var, entry] : entries_) {
    CopySample(var->value, entry.preponed_value, arena);
  }
  for (auto& [queue, entry] : queue_entries_) {
    CopyQueueSample(queue->elements, entry.preponed_elements, arena);
  }
}

const std::vector<Logic4Vec>* AssertionSampleStore::ReadQueueWithinProperty(
    const QueueObject* queue, SimTime t) const {
  if (!evaluating_property_) return nullptr;
  auto it = queue_entries_.find(queue);
  if (it == queue_entries_.end()) return nullptr;
  SampledValue decision = SampleStaticVariable(0, t, 0);
  return decision.mode == SampleMode::kDefault ? &it->second.default_elements
                                               : &it->second.preponed_elements;
}

const Logic4Vec* AssertionSampleStore::Read(const Variable* var,
                                            SimTime t) const {
  const auto& table = snapshot_ != nullptr ? snapshot_->entries : entries_;
  auto it = table.find(var);
  if (it == table.end()) return nullptr;
  SampledValue decision = SampleStaticVariable(0, StepTime(t), 0);
  return decision.mode == SampleMode::kDefault ? &it->second.default_value
                                               : &it->second.preponed_value;
}

const AssertionSampleStore::Snapshot* AssertionSampleStore::TakeSnapshot(
    SimTime t, Arena& arena) const {
  auto* snapshot = arena.Create<Snapshot>();
  snapshot->at = t;
  snapshot->entries.reserve(entries_.size());
  for (const auto& [var, entry] : entries_) {
    snapshot->entries.emplace(
        var,
        Entry{entry.default_value, OwnedSample(entry.preponed_value, arena)});
  }
  return snapshot;
}

const Logic4Vec* AssertionSampleStore::PastValue(const SampleSite& site,
                                                 uint32_t ticks_back) const {
  if (site.site == nullptr || ticks_back == 0) return nullptr;
  auto it = tick_history_.find(SiteKey{site.site, site.variant});
  if (it == tick_history_.end()) return nullptr;
  const SiteHistory& history = it->second;
  size_t index = history.recorded_at == site.now ? ticks_back : ticks_back - 1;
  if (history.values.size() <= index) return nullptr;
  return &history.values[index];
}

void AssertionSampleStore::RecordTick(const SampleSite& site,
                                      const Logic4Vec& sampled, uint32_t depth,
                                      Arena& arena) {
  if (site.site == nullptr) return;
  SiteHistory& history = tick_history_[SiteKey{site.site, site.variant}];
  Logic4Vec copy;
  CopySample(sampled, copy, arena);
  if (history.recorded_at == site.now && !history.values.empty()) {
    history.values[0] = copy;
    return;
  }
  history.values.insert(history.values.begin(), copy);
  history.recorded_at = site.now;
  if (history.values.size() > depth + 1) history.values.resize(depth + 1);
}

Logic4Vec AssertionSampleStore::OwnedSample(const Logic4Vec& sampled,
                                            Arena& arena) {
  Logic4Vec copy;
  CopySample(sampled, copy, arena);
  return copy;
}

}  // namespace delta
