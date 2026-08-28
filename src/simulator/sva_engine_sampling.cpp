#include "simulator/sva_engine_sampling.h"

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/variable.h"

namespace delta {

SequencePropertyStrength DefaultSequencePropertyStrength(AssertionKind stmt) {
  // §16.12.2: assert property and assume property evaluate a bare sequence
  // weakly; the remaining assertion statements take the strong reading.
  if (stmt == AssertionKind::kAssert || stmt == AssertionKind::kAssume) {
    return SequencePropertyStrength::kWeak;
  }
  return SequencePropertyStrength::kStrong;
}

PropertyResult EvalStrongSequenceProperty(bool has_nonempty_match) {
  // §16.12.2: the strong reading holds exactly when a nonempty match exists.
  return has_nonempty_match ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalWeakSequenceProperty(
    bool finite_prefix_witnesses_inability) {
  // §16.12.2: the weak reading holds unless some finite prefix has already
  // ruled out any match.
  return finite_prefix_witnesses_inability ? PropertyResult::kFail
                                           : PropertyResult::kPass;
}

SequencePropertyStrength NegatePropertyStrength(
    SequencePropertyStrength inner) {
  // §16.12.3: negation flips the strength — a weak underlying property becomes
  // strong under `not`, and a strong one becomes weak.
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
  // §16.5.1 / §16.10: a local variable is sampled at its current value, not at
  // its Preponed value, so its sampled value carries kCurrent just as an
  // automatic variable's does.
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue SampleActiveFreeCheckerVariable(uint64_t current_value) {
  // §16.5.1: an active free checker variable, like an automatic or local
  // variable, is sampled at its current value.
  return SampledValue{current_value, SampleMode::kCurrent};
}

SampledValue SampleActiveFreeCheckerVarPastFuture(uint64_t postponed_value) {
  // §16.5.1: a past/future value of an active free checker variable requested
  // by a sampled value function is read from the Postponed region.
  return SampledValue{postponed_value, SampleMode::kPostponed};
}

SampledValue SampleAutomaticVarPastFuture(uint64_t current_value) {
  // §16.5.1: a past/future value of an automatic variable requested by a
  // sampled value function collapses to the automatic variable's current value.
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

SampledValue ProceduralArgumentValueAfterMature(
    SampledValue captured, uint64_t /*later_underlying_value*/) {
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

uint64_t ReadProceduralConditionalGuard(uint64_t current_value,
                                        uint64_t /*sampled_value*/) {
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
  // §16.6: x and z bits make the expression false; an all-zero known value
  // is also false. Otherwise the expression is true. The bval rail carries
  // the unknown mask, so any non-zero bval forces a false interpretation.
  if (bval != 0) return false;
  return aval != 0;
}

SampledArrayElement SampleArrayElementForAssertion(uint64_t element_value) {
  return SampledArrayElement{element_value, true};
}

SampledArrayElement ArrayElementAfterArrayMutation(
    SampledArrayElement sampled) {
  // §16.6: the sampled copy remains live for the duration of the assertion
  // expression evaluation regardless of mutations to the source container.
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

// A Logic4Vec carries a pointer to its words rather than the words themselves,
// so assigning one shares storage with the value it was taken from: a later
// write through that value -- a bit-select deposit above all, which edits the
// words in place -- would show through what was meant to be a fixed sample.
// Every value this store keeps therefore owns its words. The buffer is
// allocated once per variable and reused, because Refill runs at the end of
// every time slot and MakeLogic4Vec derives the word count from the width, so a
// variable whose width has not changed needs no second allocation.
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
  if (var == nullptr || entries_.count(var) != 0) return;
  Entry entry;
  CopySample(var->value, entry.default_value, arena);
  // Before the first Refill the only value there is to read is the default one,
  // and §16.5.1 gives a time-0 read that value anyway.
  CopySample(var->value, entry.preponed_value, arena);
  entries_.emplace(var, entry);
}

void AssertionSampleStore::Refill(Arena& arena) {
  for (auto& [var, entry] : entries_) {
    CopySample(var->value, entry.preponed_value, arena);
  }
}

const Logic4Vec* AssertionSampleStore::Read(const Variable* var,
                                            SimTime t) const {
  auto it = entries_.find(var);
  if (it == entries_.end()) return nullptr;
  // SampleStaticVariable carries §16.5.1's split between time 0, which reads
  // the default sampled value, and every later time slot, which reads the
  // Preponed value. Only the mode it returns is used: SampledValue::value is a
  // uint64_t and would drop the upper bits of a variable wider than 64, so the
  // answer is the stored Logic4Vec that the mode names.
  SampledValue decision = SampleStaticVariable(0, t, 0);
  return decision.mode == SampleMode::kDefault ? &it->second.default_value
                                               : &it->second.preponed_value;
}

}  // namespace delta
