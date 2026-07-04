#include "simulator/sva_engine_sampling.h"

#include <cstdint>

#include "common/types.h"

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

SampledValue ConcurrentAssertionVariableSample(
    bool is_clocking_block_variable, uint64_t clocking_block_sampled_value,
    SampledValue ordinary_assertion_sample) {
  // §16.18: a clocking block variable is sampled only in the clocking block, so
  // the assertion reuses the value the block captured at its clocking event
  // rather than sampling the underlying signal again. That captured value is a
  // preponed sample taken at the block's clocking event.
  if (is_clocking_block_variable) {
    return SampledValue{clocking_block_sampled_value, SampleMode::kPreponed};
  }
  // A non-clocking-block variable falls back to the ordinary §16.5 sample.
  return ordinary_assertion_sample;
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

}  // namespace delta
