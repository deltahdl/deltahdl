#ifndef DELTA_SIMULATOR_SVA_ENGINE_PROPERTIES_H_
#define DELTA_SIMULATOR_SVA_ENGINE_PROPERTIES_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/sva_engine_sequences.h"

namespace delta {

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping,
                               bool antecedent_empty_match = false);

PropertyResult EvalPropertyNot(PropertyResult inner);

PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);

PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);

PropertyResult EvalPropertyIfElse(bool cond, PropertyResult then_result,
                                  bool has_else, PropertyResult else_result);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);

struct PropertyCaseBranch {
  bool selected = false;
  PropertyResult result = PropertyResult::kVacuousPass;
};

PropertyResult EvalPropertyCase(const std::vector<PropertyCaseBranch>& branches,
                                bool has_default,
                                PropertyResult default_result);

PropertyResult ResolveNonOverlapping(bool consequent_matched);

PropertyResult EvalImplicationOverMatches(
    const std::vector<PropertyResult>& per_match_consequent);

PropertyResult EvalPropertyImplies(PropertyResult antecedent,
                                   PropertyResult consequent);

PropertyResult EvalPropertyIff(PropertyResult a, PropertyResult b);

PropertyResult EvalFollowedBy(bool antecedent, bool consequent,
                              bool non_overlapping,
                              bool antecedent_empty_match = false);

PropertyResult ResolveFollowedByNonOverlapping(bool consequent_matched);

PropertyResult EvalNexttime(bool strong, bool target_tick_reachable,
                            PropertyResult inner_at_target);

bool NexttimeTargetReachable(uint64_t index, uint64_t future_clock_ticks);

inline constexpr int kAlwaysUnboundedMax = -1;

PropertyResult EvalAlways(bool strong, bool all_covered_ticks_present,
                          bool inner_holds_at_present_ticks);

bool AlwaysRangeCovers(int index, int range_min, int range_max);

bool AlwaysStrongTicksAllPresent(int range_max, int future_clock_ticks);

inline constexpr int kUntilRhsNever = -1;

bool UntilLeftHoldsRequired(bool overlapping, int lhs_run_length,
                            int first_rhs_index, int trace_length);

PropertyResult EvalUntil(bool strong, bool rhs_holds_eventually,
                         bool lhs_holds_required);

PropertyResult EvalEventually(bool strong, bool inner_holds_within_range,
                              bool all_range_ticks_present);

PropertyResult EvalAbortAccept(bool abort_condition, PropertyResult inner);

PropertyResult EvalAbortReject(bool abort_condition, PropertyResult inner);

PropertyResult EvalNestedAbort(bool outer_forces_true, bool outer_condition,
                               bool inner_forces_true, bool inner_condition,
                               PropertyResult inner_property);

bool AbortConditionUsesSampledValues();

bool AbortConditionEvaluatedAtClockingEventOnly(bool synchronous_abort);

PropertyResult EvalMulticlockedSequenceAsProperty(bool sequence_has_match);

PropertyResult EvalMulticlockedAnd(bool left_operand_has_match,
                                   bool right_operand_has_match);

inline constexpr uint64_t kNoMulticlockTick = ~static_cast<uint64_t>(0);

uint64_t NearestClockTickAtOrAfter(uint64_t from,
                                   const std::vector<uint64_t>& clock_ticks,
                                   bool inclusive);

uint64_t MulticlockedConsequentEvalTick(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

bool MulticlockedImplicationChecksImmediately(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

uint64_t MulticlockedIfBranchEvalTick(
    uint64_t condition_time, const std::vector<uint64_t>& branch_clock_ticks);

struct LocalVarInitCopy {
  size_t leading_clock_index;
  uint64_t init_tick;
};

uint64_t SinglyClockedLocalInitTick(uint64_t attempt_begin);

uint64_t MulticlockedLocalInitTick(
    uint64_t attempt_begin, const std::vector<uint64_t>& leading_clock_ticks);

size_t LocalVarCopyCount(size_t distinct_semantic_leading_clocks);

std::vector<LocalVarInitCopy> MulticlockedLocalInitCopies(
    uint64_t attempt_begin,
    const std::vector<std::vector<uint64_t>>& per_leading_clock_ticks);

bool NonvacuousSequenceForm();

bool NonvacuousPassthrough(bool inner_nonvacuous);

bool NonvacuousDisjunctiveForm(bool left_nonvacuous, bool right_nonvacuous);

bool NonvacuousIfElse(bool guard_holds, bool then_nonvacuous, bool has_else,
                      bool else_nonvacuous);

bool NonvacuousSequencePrecondition(bool antecedent_has_match,
                                    bool consequent_nonvacuous);

bool NonvacuousNexttime(bool target_clock_event_reachable,
                        bool inner_nonvacuous_at_target);

bool NonvacuousAlways(bool inner_nonvacuous_at_some_covered_event,
                      bool inner_fails_at_prior_covered_event);

bool NonvacuousEventually(bool inner_nonvacuous_at_some_covered_event,
                          bool inner_holds_at_prior_covered_event);

bool NonvacuousUntil(bool overlapping, bool left_nonvacuous_at_witness,
                     bool right_nonvacuous_at_witness,
                     bool right_holds_at_prior_event,
                     bool left_holds_at_all_prior_events);

bool NonvacuousImplies(bool antecedent_true, bool antecedent_nonvacuous,
                       bool consequent_nonvacuous);

bool NonvacuousAbortOrDisable(bool inner_nonvacuous,
                              bool condition_holds_at_any_evaluated_step);

bool NonvacuousCase(bool a_branch_selected, bool selected_stmt_nonvacuous);

bool PropertySucceedsNonvacuously(bool property_true, bool attempt_nonvacuous);

}  // namespace delta

#endif
