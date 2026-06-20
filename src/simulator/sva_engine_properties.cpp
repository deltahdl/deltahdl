#include "simulator/sva_engine_properties.h"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace delta {

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping) {
  // §16.12.7: with no antecedent match the implication holds vacuously. For the
  // overlapped form (|->) the consequent is evaluated at the end point of the
  // match, so the verdict is the consequent's own. For the nonoverlapped form
  // (|=>) the consequent starts one tick later, so the verdict is deferred and
  // settled later by ResolveNonOverlapping.
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
  // §16.12.16: linear search in source order. The first item whose expression
  // matches the case expression is the only property_expr evaluated, and the
  // search terminates at that point, so a later matching item never overrides
  // it. Default items are not part of `branches`, so the scan structurally
  // ignores any default while looking for a match.
  for (const auto& branch : branches) {
    if (branch.selected) return branch.result;
  }
  // Every comparison failed. If a default item is given its property_expr is
  // executed and supplies the verdict; with no default item nothing is
  // evaluated and the case property holds vacuously.
  if (has_default) return default_result;
  return PropertyResult::kVacuousPass;
}

PropertyResult ResolveNonOverlapping(bool consequent_matched) {
  // §16.12.7: settles a deferred nonoverlapped (|=>) implication at the tick
  // after the antecedent match, where the consequent is finally evaluated;
  // this realizes the equivalence of `seq |=> p` with `seq ##1 `true |-> p`.
  return consequent_matched ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalPropertyImplies(PropertyResult antecedent,
                                   PropertyResult consequent) {
  // §16.12.8: holds when the antecedent does not hold or the consequent holds.
  // A vacuous pass counts as the operand holding, mirroring EvalPropertyOr.
  bool ant_holds = antecedent == PropertyResult::kPass ||
                   antecedent == PropertyResult::kVacuousPass;
  bool con_holds = consequent == PropertyResult::kPass ||
                   consequent == PropertyResult::kVacuousPass;
  return (!ant_holds || con_holds) ? PropertyResult::kPass
                                   : PropertyResult::kFail;
}

PropertyResult EvalPropertyIff(PropertyResult a, PropertyResult b) {
  // §16.12.8: holds when the two operands' verdicts agree — both hold or both
  // fail to hold. A vacuous pass counts as the operand holding.
  bool a_holds =
      a == PropertyResult::kPass || a == PropertyResult::kVacuousPass;
  bool b_holds =
      b == PropertyResult::kPass || b == PropertyResult::kVacuousPass;
  return (a_holds == b_holds) ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalFollowedBy(bool antecedent, bool consequent,
                              bool non_overlapping) {
  // §16.12.9: apply the duality with the implication operators directly —
  // `s #-# p` ≡ not (s |-> not p) and `s #=# p` ≡ not (s |=> not p). Negate the
  // consequent, evaluate the matching §16.12.7 implication, then negate the
  // verdict. A missing antecedent match makes the dual implication hold
  // vacuously, which negates to a definite fail — capturing the requirement
  // that the antecedent shall have at least one successful match. A deferred
  // (nonoverlapped) implication stays pending here and is settled later by
  // ResolveFollowedByNonOverlapping.
  PropertyResult implied =
      EvalImplication(antecedent, !consequent, non_overlapping);
  if (implied == PropertyResult::kPending) return PropertyResult::kPending;
  return EvalPropertyNot(implied);
}

PropertyResult ResolveFollowedByNonOverlapping(bool consequent_matched) {
  // §16.12.9: settle the deferred nonoverlapped followed-by at the tick after
  // the antecedent match. By the duality the dual implication is settled on the
  // negated consequent and that verdict is negated, so a holding consequent
  // yields a pass.
  return EvalPropertyNot(ResolveNonOverlapping(!consequent_matched));
}

PropertyResult EvalNexttime(bool strong, bool target_tick_reachable,
                            PropertyResult inner_at_target) {
  // §16.12.10: when the target tick exists the nexttime verdict is the inner
  // property_expr's verdict at that tick. When the target tick is unreachable
  // the strength decides: the weak form holds (no further tick can disprove the
  // obligation) while the strong form fails (the required tick never arrived).
  if (target_tick_reachable) return inner_at_target;
  return strong ? PropertyResult::kFail : PropertyResult::kPass;
}

bool NexttimeTargetReachable(uint64_t index, uint64_t future_clock_ticks) {
  // §16.12.10: counting starts at the current time step, so the index-`n`
  // target is the tick reached after `n` further ticks. Index 0 targets the
  // current step and is always reachable — the alignment-operator behavior —
  // while the non-indexed next-tick case is index 1.
  return future_clock_ticks >= index;
}

// §16.12.11: weak `always` and strong `s_always` differ only in how they treat
// covered clock ticks that are missing. The weak form does not require the
// ticks within its range to exist, so it depends solely on the inner
// property_expr holding at every present tick. The strong form additionally
// requires every covered tick to exist, failing when any is absent even if the
// inner verdict at the present ticks was true.
PropertyResult EvalAlways(bool strong, bool all_covered_ticks_present,
                          bool inner_holds_at_present_ticks) {
  if (strong && !all_covered_ticks_present) {
    return PropertyResult::kFail;
  }
  return inner_holds_at_present_ticks ? PropertyResult::kPass
                                      : PropertyResult::kFail;
}

// §16.12.11: a tick is covered when its index is at least the minimum bound
// and, unless the maximum is unbounded, at most the maximum bound. Counting
// starts at the current time step.
bool AlwaysRangeCovers(int index, int range_min, int range_max) {
  if (index < range_min) {
    return false;
  }
  if (range_max == kAlwaysUnboundedMax) {
    return true;
  }
  return index <= range_max;
}

// §16.12.11: with counting starting at the current time step, every covered
// tick up to `range_max` exists when that many further ticks are available.
bool AlwaysStrongTicksAllPresent(int range_max, int future_clock_ticks) {
  return range_max <= future_clock_ticks;
}

// §16.12.12: the left operand is required over a prefix of the trace, so a run
// of consecutive holding ticks from the start covers the requirement exactly
// when it is at least as long as the required prefix. The non-overlapping forms
// stop before the first right-operand tick (so the left operand need not hold
// there, and need not hold at all when the right operand holds at the starting
// tick); the overlapping forms extend through that tick; and when the right
// operand never holds the requirement spans the whole trace.
bool UntilLeftHoldsRequired(bool overlapping, int lhs_run_length,
                            int first_rhs_index, int trace_length) {
  int required_count;
  if (first_rhs_index == kUntilRhsNever) {
    required_count = trace_length;
  } else if (overlapping) {
    required_count = first_rhs_index + 1;
  } else {
    required_count = first_rhs_index;
  }
  return lhs_run_length >= required_count;
}

// §16.12.12: a strong until additionally requires a current or future tick at
// which the right operand holds, so it fails when none exists even if the left
// operand held throughout. A weak until ignores that requirement and settles on
// whether the left operand met its obligation.
PropertyResult EvalUntil(bool strong, bool rhs_holds_eventually,
                         bool lhs_holds_required) {
  if (strong && !rhs_holds_eventually) {
    return PropertyResult::kFail;
  }
  return lhs_holds_required ? PropertyResult::kPass : PropertyResult::kFail;
}

// §16.12.13: a strong eventually holds exactly when the inner property_expr
// holds at some current or future clock tick within the range; with no such
// witness it fails. A weak eventually also holds when the range's ticks do not
// all exist, because the weak form does not require those later ticks to be
// present.
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
  // §16.12.14: a true abort condition forces the accept forms to true and takes
  // precedence over the underlying property_expr's verdict.
  if (abort_condition) return PropertyResult::kPass;
  return inner;
}

PropertyResult EvalAbortReject(bool abort_condition, PropertyResult inner) {
  // §16.12.14: a true abort condition forces the reject forms to false and
  // takes precedence over the underlying verdict. This is the dual of
  // EvalAbortAccept: reject_on(c) p is not(accept_on(c) not p), so a true
  // condition that accepts not(p) negates back to a fail, and a false condition
  // leaves the underlying verdict unchanged.
  if (abort_condition) return PropertyResult::kFail;
  return inner;
}

PropertyResult EvalNestedAbort(bool outer_forces_true, bool outer_condition,
                               bool inner_forces_true, bool inner_condition,
                               PropertyResult inner_property) {
  // §16.12.14: apply the inner abort operator first, then the outer one.
  // Because the outer operator forces its own outcome whenever its condition is
  // true, it overrides whatever the inner operator decided — so when both
  // conditions become true in the same time step the outermost operator takes
  // precedence.
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
  // §16.13.2: evaluated as a property at a point, a multiclocked sequence is
  // true exactly when a match of the sequence begins at that point. The verdict
  // is definite — there is no pending reading at the multiclocked-property
  // level.
  return sequence_has_match ? PropertyResult::kPass : PropertyResult::kFail;
}

PropertyResult EvalMulticlockedAnd(bool left_operand_has_match,
                                   bool right_operand_has_match) {
  // §16.13.2: each operand is evaluated as a property on its own clock and the
  // multiclocked conjunction holds exactly when both operand properties hold,
  // reusing the §16.12.4 Boolean property `and` over the two operand verdicts.
  return EvalPropertyAnd(
      EvalMulticlockedSequenceAsProperty(left_operand_has_match),
      EvalMulticlockedSequenceAsProperty(right_operand_has_match));
}

uint64_t NearestClockTickAtOrAfter(uint64_t from,
                                   const std::vector<uint64_t>& clock_ticks,
                                   bool inclusive) {
  // §16.13.2: ticks are in increasing time order; the first that qualifies is
  // the nearest. The inclusive reading admits a tick coincident with `from`.
  for (uint64_t tick : clock_ticks) {
    if (tick > from || (inclusive && tick == from)) return tick;
  }
  return kNoMulticlockTick;
}

uint64_t MulticlockedConsequentEvalTick(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping) {
  // §16.13.2: the overlapping implication (|->) may check at a tick coincident
  // with the antecedent end; the nonoverlapping implication (|=>) advances to a
  // strictly future tick.
  return NearestClockTickAtOrAfter(antecedent_end_time, consequent_clock_ticks,
                                   /*inclusive=*/overlapping);
}

bool MulticlockedImplicationChecksImmediately(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping) {
  // §16.13.2: only the overlapping form checks immediately, and only when the
  // consequent clock actually ticks at the antecedent match end.
  if (!overlapping) return false;
  return MulticlockedConsequentEvalTick(antecedent_end_time,
                                        consequent_clock_ticks,
                                        overlapping) == antecedent_end_time;
}

uint64_t MulticlockedIfBranchEvalTick(
    uint64_t condition_time, const std::vector<uint64_t>& branch_clock_ticks) {
  // §16.13.2: both the possibly-overlapping then-branch and the non-strictly
  // subsequent else-branch admit a branch-clock tick coincident with the
  // condition check, so each is evaluated at the nearest tick at or after it.
  return NearestClockTickAtOrAfter(condition_time, branch_clock_ticks,
                                   /*inclusive=*/true);
}

uint64_t SinglyClockedLocalInitTick(uint64_t attempt_begin) {
  // §16.13.7: the evaluation attempt of a singly clocked instance always begins
  // at a tick of the single governing clock, and the initialization assignment
  // is performed at that beginning — so the init time is the attempt-begin
  // time.
  return attempt_begin;
}

uint64_t MulticlockedLocalInitTick(
    uint64_t attempt_begin, const std::vector<uint64_t>& leading_clock_ticks) {
  // §16.13.7: schedule the init assignment at the earliest
  // semantic-leading-clock tick at or after the attempt begin. A tick
  // coincident with the begin qualifies, reusing the §16.13.2 at-or-after
  // (inclusive) reading.
  return NearestClockTickAtOrAfter(attempt_begin, leading_clock_ticks,
                                   /*inclusive=*/true);
}

size_t LocalVarCopyCount(size_t distinct_semantic_leading_clocks) {
  // §16.13.7: one copy of the local variable is created per distinct semantic
  // leading clock of the instance.
  return distinct_semantic_leading_clocks;
}

std::vector<LocalVarInitCopy> MulticlockedLocalInitCopies(
    uint64_t attempt_begin,
    const std::vector<std::vector<uint64_t>>& per_leading_clock_ticks) {
  // §16.13.7: build one copy per semantic leading clock. Each copy's init
  // assignment is scheduled independently at the earliest tick of its own
  // leading clock at or after the attempt begin; that copy then governs the
  // subproperty associated with the same leading clock.
  std::vector<LocalVarInitCopy> copies;
  copies.reserve(per_leading_clock_ticks.size());
  for (size_t i = 0; i < per_leading_clock_ticks.size(); ++i) {
    copies.push_back({i, MulticlockedLocalInitTick(
                             attempt_begin, per_leading_clock_ticks[i])});
  }
  return copies;
}

bool NonvacuousSequenceForm() {
  // §16.14.8(a)(b)(c): a sequence, strong(sequence_expr), and
  // weak(sequence_expr) attempt are nonvacuous unconditionally.
  return true;
}

bool NonvacuousPassthrough(bool inner_nonvacuous) {
  // §16.14.8(d)(i): `not property_expr` and a property instance simply carry
  // the nonvacuity of their one underlying attempt.
  return inner_nonvacuous;
}

bool NonvacuousDisjunctiveForm(bool left_nonvacuous, bool right_nonvacuous) {
  // §16.14.8(e)(f)(aa): `or`, `and`, and `iff` are nonvacuous when either
  // operand's underlying attempt is nonvacuous.
  return left_nonvacuous || right_nonvacuous;
}

bool NonvacuousIfElse(bool guard_holds, bool then_nonvacuous, bool has_else,
                      bool else_nonvacuous) {
  // §16.14.8(g): a held guard takes the then-branch; otherwise the else-branch
  // is taken when present, and a guardless miss holds vacuously.
  if (guard_holds) return then_nonvacuous;
  return has_else && else_nonvacuous;
}

bool NonvacuousSequencePrecondition(bool antecedent_has_match,
                                    bool consequent_nonvacuous) {
  // §16.14.8(h)(j)(k): the implication and followed-by forms need an antecedent
  // match point and a nonvacuous consequent attempt from that point.
  return antecedent_has_match && consequent_nonvacuous;
}

bool NonvacuousNexttime(bool target_clock_event_reachable,
                        bool inner_nonvacuous_at_target) {
  // §16.14.8(l)(m)(n)(o): the targeted future clock event must exist and the
  // subproperty attempt beginning there must be nonvacuous.
  return target_clock_event_reachable && inner_nonvacuous_at_target;
}

bool NonvacuousAlways(bool inner_nonvacuous_at_some_covered_event,
                      bool inner_fails_at_prior_covered_event) {
  // §16.14.8(p)(q)(r): a covered clock event must witness a nonvacuous
  // subproperty attempt, with no earlier covered failure.
  return inner_nonvacuous_at_some_covered_event &&
         !inner_fails_at_prior_covered_event;
}

bool NonvacuousEventually(bool inner_nonvacuous_at_some_covered_event,
                          bool inner_holds_at_prior_covered_event) {
  // §16.14.8(s)(t)(u): a covered clock event must witness a nonvacuous
  // subproperty attempt, with the subproperty not already holding earlier.
  return inner_nonvacuous_at_some_covered_event &&
         !inner_holds_at_prior_covered_event;
}

bool NonvacuousUntil(bool overlapping, bool left_nonvacuous_at_witness,
                     bool right_nonvacuous_at_witness,
                     bool right_holds_at_prior_event,
                     bool left_holds_at_all_prior_events) {
  // §16.14.8(v)(w)(x)(y): the overlapping forms witness on the left operand
  // alone; the non-overlapping forms witness on either operand. In both cases
  // the right operand must not have held earlier and the left operand must have
  // held at every earlier clock event.
  bool witness =
      overlapping ? left_nonvacuous_at_witness
                  : (left_nonvacuous_at_witness || right_nonvacuous_at_witness);
  return witness && !right_holds_at_prior_event &&
         left_holds_at_all_prior_events;
}

bool NonvacuousImplies(bool antecedent_true, bool antecedent_nonvacuous,
                       bool consequent_nonvacuous) {
  // §16.14.8(z): the antecedent attempt must be both true and nonvacuous, and
  // the consequent attempt must be nonvacuous.
  return antecedent_true && antecedent_nonvacuous && consequent_nonvacuous;
}

bool NonvacuousAbortOrDisable(bool inner_nonvacuous,
                              bool condition_holds_at_any_evaluated_step) {
  // §16.14.8(ab)(ac)(ad)(ae)(ag): a nonvacuous underlying attempt whose
  // abort/disable condition never held across the steps it was evaluated at.
  return inner_nonvacuous && !condition_holds_at_any_evaluated_step;
}

bool NonvacuousCase(bool a_branch_selected, bool selected_stmt_nonvacuous) {
  // §16.14.8(af): a case item (a matching expression_or_dist or the default)
  // must be selected and its property_stmt attempt must be nonvacuous.
  return a_branch_selected && selected_stmt_nonvacuous;
}

bool PropertySucceedsNonvacuously(bool property_true, bool attempt_nonvacuous) {
  // §16.14.8: a nonvacuous success requires both a true verdict and a
  // nonvacuous attempt.
  return property_true && attempt_nonvacuous;
}

}  // namespace delta
