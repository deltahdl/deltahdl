#include "simulator/sva_engine_properties.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/sva_engine_sequences.h"

namespace delta {

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping,
                               bool antecedent_empty_match) {
  if (!antecedent) return PropertyResult::kVacuousPass;
  if (non_overlapping && !antecedent_empty_match) {
    return PropertyResult::kPending;
  }
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

PropertyResult EvalPropertyIfElse(bool cond, PropertyResult then_result,
                                  bool has_else, PropertyResult else_result) {
  if (cond) return then_result;
  if (has_else) return else_result;
  return PropertyResult::kVacuousPass;
}

PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner) {
  if (disable_cond) return PropertyResult::kVacuousPass;
  return inner;
}

PropertyResult EvalPropertyCase(const std::vector<PropertyCaseBranch>& branches,
                                bool has_default,
                                PropertyResult default_result) {
  for (const auto& branch : branches) {
    if (branch.selected) return branch.result;
  }
  if (has_default) return default_result;
  return PropertyResult::kVacuousPass;
}

PropertyResult ResolveNonOverlapping(bool consequent_matched) {
  return consequent_matched ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalImplicationOverMatches(
    const std::vector<PropertyResult>& per_match_consequent) {
  if (per_match_consequent.empty()) return PropertyResult::kVacuousPass;
  for (PropertyResult consequent : per_match_consequent) {
    if (consequent == PropertyResult::kFail) return PropertyResult::kFail;
  }
  return PropertyResult::kPass;
}

PropertyResult EvalPropertyImplies(PropertyResult antecedent,
                                   PropertyResult consequent) {
  bool ant_holds = antecedent == PropertyResult::kPass ||
                   antecedent == PropertyResult::kVacuousPass;
  bool con_holds = consequent == PropertyResult::kPass ||
                   consequent == PropertyResult::kVacuousPass;
  return (!ant_holds || con_holds) ? PropertyResult::kPass
                                   : PropertyResult::kFail;
}

PropertyResult EvalPropertyIff(PropertyResult a, PropertyResult b) {
  bool a_holds =
      a == PropertyResult::kPass || a == PropertyResult::kVacuousPass;
  bool b_holds =
      b == PropertyResult::kPass || b == PropertyResult::kVacuousPass;
  return (a_holds == b_holds) ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalFollowedBy(bool antecedent, bool consequent,
                              bool non_overlapping,
                              bool antecedent_empty_match) {
  PropertyResult implied = EvalImplication(
      antecedent, !consequent, non_overlapping, antecedent_empty_match);
  if (implied == PropertyResult::kPending) return PropertyResult::kPending;
  return EvalPropertyNot(implied);
}

PropertyResult ResolveFollowedByNonOverlapping(bool consequent_matched) {
  return EvalPropertyNot(ResolveNonOverlapping(!consequent_matched));
}

PropertyResult EvalNexttime(bool strong, bool target_tick_reachable,
                            PropertyResult inner_at_target) {
  if (target_tick_reachable) return inner_at_target;
  return strong ? PropertyResult::kFail : PropertyResult::kPass;
}

bool NexttimeTargetReachable(uint64_t index, uint64_t future_clock_ticks) {
  return future_clock_ticks >= index;
}

PropertyResult EvalAlways(bool strong, bool all_covered_ticks_present,
                          bool inner_holds_at_present_ticks) {
  if (strong && !all_covered_ticks_present) {
    return PropertyResult::kFail;
  }
  return inner_holds_at_present_ticks ? PropertyResult::kPass
                                      : PropertyResult::kFail;
}

bool AlwaysRangeCovers(int index, int range_min, int range_max) {
  if (index < range_min) {
    return false;
  }
  if (range_max == kAlwaysUnboundedMax) {
    return true;
  }
  return index <= range_max;
}

bool AlwaysStrongTicksAllPresent(int range_max, int future_clock_ticks) {
  return range_max <= future_clock_ticks;
}

bool UntilLeftHoldsRequired(bool overlapping, int lhs_run_length,
                            int first_rhs_index, int trace_length) {
  int required_count = 0;
  if (first_rhs_index == kUntilRhsNever) {
    required_count = trace_length;
  } else if (overlapping) {
    required_count = first_rhs_index + 1;
  } else {
    required_count = first_rhs_index;
  }
  return lhs_run_length >= required_count;
}

PropertyResult EvalUntil(bool strong, bool rhs_holds_eventually,
                         bool lhs_holds_required) {
  if (strong && !rhs_holds_eventually) {
    return PropertyResult::kFail;
  }
  return lhs_holds_required ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalEventually(bool strong, bool inner_holds_within_range,
                              bool all_range_ticks_present) {
  if (inner_holds_within_range) {
    return PropertyResult::kPass;
  }
  if (strong) {
    return PropertyResult::kFail;
  }
  return all_range_ticks_present ? PropertyResult::kFail
                                 : PropertyResult::kPass;
}

PropertyResult EvalAbortAccept(bool abort_condition, PropertyResult inner) {
  if (abort_condition) return PropertyResult::kPass;
  return inner;
}

PropertyResult EvalAbortReject(bool abort_condition, PropertyResult inner) {
  if (abort_condition) return PropertyResult::kFail;
  return inner;
}

PropertyResult EvalNestedAbort(bool outer_forces_true, bool outer_condition,
                               bool inner_forces_true, bool inner_condition,
                               PropertyResult inner_property) {
  PropertyResult after_inner =
      inner_forces_true ? EvalAbortAccept(inner_condition, inner_property)
                        : EvalAbortReject(inner_condition, inner_property);
  return outer_forces_true ? EvalAbortAccept(outer_condition, after_inner)
                           : EvalAbortReject(outer_condition, after_inner);
}

bool AbortConditionUsesSampledValues() { return true; }

bool AbortConditionEvaluatedAtClockingEventOnly(bool synchronous_abort) {
  return synchronous_abort;
}

PropertyResult EvalMulticlockedSequenceAsProperty(bool sequence_has_match) {
  return sequence_has_match ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalMulticlockedAnd(bool left_operand_has_match,
                                   bool right_operand_has_match) {
  return EvalPropertyAnd(
      EvalMulticlockedSequenceAsProperty(left_operand_has_match),
      EvalMulticlockedSequenceAsProperty(right_operand_has_match));
}

uint64_t NearestClockTickAtOrAfter(uint64_t from,
                                   const std::vector<uint64_t>& clock_ticks,
                                   bool inclusive) {
  for (uint64_t tick : clock_ticks) {
    if (tick > from || (inclusive && tick == from)) return tick;
  }
  return kNoMulticlockTick;
}

uint64_t MulticlockedConsequentEvalTick(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping) {
  return NearestClockTickAtOrAfter(antecedent_end_time, consequent_clock_ticks,
                                   overlapping);
}

bool MulticlockedImplicationChecksImmediately(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping) {
  if (!overlapping) return false;
  return MulticlockedConsequentEvalTick(antecedent_end_time,
                                        consequent_clock_ticks,
                                        overlapping) == antecedent_end_time;
}

uint64_t MulticlockedIfBranchEvalTick(
    uint64_t condition_time, const std::vector<uint64_t>& branch_clock_ticks) {
  return NearestClockTickAtOrAfter(condition_time, branch_clock_ticks, true);
}

uint64_t SinglyClockedLocalInitTick(uint64_t attempt_begin) {
  return attempt_begin;
}

uint64_t MulticlockedLocalInitTick(
    uint64_t attempt_begin, const std::vector<uint64_t>& leading_clock_ticks) {
  return NearestClockTickAtOrAfter(attempt_begin, leading_clock_ticks, true);
}

size_t LocalVarCopyCount(size_t distinct_semantic_leading_clocks) {
  return distinct_semantic_leading_clocks;
}

std::vector<LocalVarInitCopy> MulticlockedLocalInitCopies(
    uint64_t attempt_begin,
    const std::vector<std::vector<uint64_t>>& per_leading_clock_ticks) {
  std::vector<LocalVarInitCopy> copies;
  copies.reserve(per_leading_clock_ticks.size());
  for (size_t i = 0; i < per_leading_clock_ticks.size(); ++i) {
    copies.push_back({i, MulticlockedLocalInitTick(
                             attempt_begin, per_leading_clock_ticks[i])});
  }
  return copies;
}

bool NonvacuousSequenceForm() { return true; }

bool NonvacuousPassthrough(bool inner_nonvacuous) { return inner_nonvacuous; }

bool NonvacuousDisjunctiveForm(bool left_nonvacuous, bool right_nonvacuous) {
  return left_nonvacuous || right_nonvacuous;
}

bool NonvacuousIfElse(bool guard_holds, bool then_nonvacuous, bool has_else,
                      bool else_nonvacuous) {
  if (guard_holds) return then_nonvacuous;
  return has_else && else_nonvacuous;
}

bool NonvacuousSequencePrecondition(bool antecedent_has_match,
                                    bool consequent_nonvacuous) {
  return antecedent_has_match && consequent_nonvacuous;
}

bool NonvacuousNexttime(bool target_clock_event_reachable,
                        bool inner_nonvacuous_at_target) {
  return target_clock_event_reachable && inner_nonvacuous_at_target;
}

bool NonvacuousAlways(bool inner_nonvacuous_at_some_covered_event,
                      bool inner_fails_at_prior_covered_event) {
  return inner_nonvacuous_at_some_covered_event &&
         !inner_fails_at_prior_covered_event;
}

bool NonvacuousEventually(bool inner_nonvacuous_at_some_covered_event,
                          bool inner_holds_at_prior_covered_event) {
  return inner_nonvacuous_at_some_covered_event &&
         !inner_holds_at_prior_covered_event;
}

bool NonvacuousUntil(bool overlapping, bool left_nonvacuous_at_witness,
                     bool right_nonvacuous_at_witness,
                     bool right_holds_at_prior_event,
                     bool left_holds_at_all_prior_events) {
  bool witness =
      overlapping ? left_nonvacuous_at_witness
                  : (left_nonvacuous_at_witness || right_nonvacuous_at_witness);
  return witness && !right_holds_at_prior_event &&
         left_holds_at_all_prior_events;
}

bool NonvacuousImplies(bool antecedent_true, bool antecedent_nonvacuous,
                       bool consequent_nonvacuous) {
  return antecedent_true && antecedent_nonvacuous && consequent_nonvacuous;
}

bool NonvacuousAbortOrDisable(bool inner_nonvacuous,
                              bool condition_holds_at_any_evaluated_step) {
  return inner_nonvacuous && !condition_holds_at_any_evaluated_step;
}

bool NonvacuousCase(bool a_branch_selected, bool selected_stmt_nonvacuous) {
  return a_branch_selected && selected_stmt_nonvacuous;
}

bool PropertySucceedsNonvacuously(bool property_true, bool attempt_nonvacuous) {
  return property_true && attempt_nonvacuous;
}

}  // namespace delta
