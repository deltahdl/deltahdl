#include "simulator/sva_engine.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/scheduler.h"

namespace delta {

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

void AdvanceSequence(SequenceAttempt& sa) {
  if (sa.delay_remaining > 0) {
    --sa.delay_remaining;
  }
}

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

bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals) {
  if (vals.empty()) return seq.rep_min == 0;
  uint32_t match_count = 0;
  for (auto v : vals) {
    if (seq.expr_check && seq.expr_check(v)) {
      ++match_count;
    }
  }

  bool last_matches = seq.expr_check && seq.expr_check(vals.back());
  return last_matches && match_count >= seq.rep_min &&
         match_count <= seq.rep_max;
}

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

bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals) {
  if (vals.size() <= seq.delay_cycles) return false;
  uint64_t check_val = vals[seq.delay_cycles];
  return seq.expr_check && seq.expr_check(check_val);
}

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay) {
  EmptyConcatResult result;
  // (empty ##0 seq) and (seq ##0 empty): a length-0 endpoint can never align
  // with the neighboring sequence at the same time step, so neither matches.
  if (delay == 0) {
    result.matchable = false;
    return result;
  }
  // With delay n > 0 the empty operand contributes nothing, and the leftover
  // delay collapses onto the surviving operand as ##(n-1).
  result.matchable = true;
  result.effective_delay = delay - 1;
  // (seq ##n empty) is equivalent to (seq ##(n-1) `true), extending the match
  // one tick past seq; (empty ##n seq) is equivalent to (##(n-1) seq), which
  // merely prefixes the reduced delay.
  result.append_true = (side == EmptyConcatSide::kEmptyRight);
  return result;
}

bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match) {
  // A repetition that can take zero iterations is the disjunction of its empty
  // and nonempty cases; otherwise only the nonempty case is reachable.
  if (rep_min == 0) return empty_case_match || nonempty_case_match;
  return nonempty_case_match;
}

bool EvalSequenceAnd(bool a_match, bool b_match) { return a_match && b_match; }

SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time) {
  SequenceAndMatch result;
  result.matched = a_match && b_match;
  // The operands share a start time; the composite completes when the slower
  // operand does, i.e. at the later of the two end times.
  result.end_time = std::max(a_end_time, b_end_time);
  return result;
}

bool EvalSequenceOr(bool a_match, bool b_match) { return a_match || b_match; }

SequenceOrMatches EvalSequenceOrMatches(
    const std::vector<uint32_t>& a_end_times,
    const std::vector<uint32_t>& b_end_times) {
  SequenceOrMatches result;
  // The match set is the union of the two operands' matches: each operand match
  // carries through unchanged, keeping its own end time. Matches are not merged,
  // so both operands matching on the same tick yields two separate entries.
  result.end_times = a_end_times;
  result.end_times.insert(result.end_times.end(), b_end_times.begin(),
                          b_end_times.end());
  result.matched = !result.end_times.empty();
  return result;
}

FirstMatchMatches EvalFirstMatch(
    const std::vector<uint32_t>& operand_end_times) {
  FirstMatchMatches result;
  // No match of the operand means no match of first_match.
  if (operand_end_times.empty()) return result;
  // The earliest ending clock tick among the operand's matches selects the
  // first match; every match ending later is discarded.
  uint32_t earliest = *std::min_element(operand_end_times.begin(),
                                        operand_end_times.end());
  // Ties at the earliest ending tick are all retained: when several operand
  // matches end on that tick, each one is a match of first_match.
  for (uint32_t end_time : operand_end_times) {
    if (end_time == earliest) result.end_times.push_back(end_time);
  }
  result.matched = true;
  return result;
}

bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len) {
  return a_match && b_match && a_len == b_len;
}

bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values) {
  return std::all_of(values.begin(), values.end(), check);
}

SequenceWithinMatch EvalSequenceWithin(bool inner_match, uint32_t inner_start,
                                       uint32_t inner_end, bool outer_match,
                                       uint32_t outer_start,
                                       uint32_t outer_end) {
  SequenceWithinMatch result;
  // seq1 within seq2 ≡ (1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect seq2: both
  // operands match and the match of seq1 falls inside the match of seq2. The
  // leading 1[*0:$] lets seq1 start no earlier than seq2's start, and the
  // trailing 1[*0:$] lets seq1 complete no later than seq2's completion.
  result.matched = inner_match && outer_match && inner_start >= outer_start &&
                   inner_end <= outer_end;
  // The intersection makes the composite cover seq2's whole interval, so it
  // completes at seq2's match point.
  result.end_time = outer_end;
  return result;
}

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
  // §16.12.10: counting starts at the current time step, so the index-`n` target
  // is the tick reached after `n` further ticks. Index 0 targets the current
  // step and is always reachable — the alignment-operator behavior — while the
  // non-indexed next-tick case is index 1.
  return future_clock_ticks >= index;
}

// §16.12.11: weak `always` and strong `s_always` differ only in how they treat
// covered clock ticks that are missing. The weak form does not require the ticks
// within its range to exist, so it depends solely on the inner property_expr
// holding at every present tick. The strong form additionally requires every
// covered tick to exist, failing when any is absent even if the inner verdict at
// the present ticks was true.
PropertyResult EvalAlways(bool strong, bool all_covered_ticks_present,
                          bool inner_holds_at_present_ticks) {
  if (strong && !all_covered_ticks_present) {
    return PropertyResult::kFail;
  }
  return inner_holds_at_present_ticks ? PropertyResult::kPass
                                      : PropertyResult::kFail;
}

// §16.12.11: a tick is covered when its index is at least the minimum bound and,
// unless the maximum is unbounded, at most the maximum bound. Counting starts at
// the current time step.
bool AlwaysRangeCovers(int index, int range_min, int range_max) {
  if (index < range_min) {
    return false;
  }
  if (range_max == kAlwaysUnboundedMax) {
    return true;
  }
  return index <= range_max;
}

// §16.12.11: with counting starting at the current time step, every covered tick
// up to `range_max` exists when that many further ticks are available.
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

// §16.12.13: a strong eventually holds exactly when the inner property_expr holds
// at some current or future clock tick within the range; with no such witness it
// fails. A weak eventually also holds when the range's ticks do not all exist,
// because the weak form does not require those later ticks to be present.
PropertyResult EvalEventually(bool strong, bool inner_holds_within_range,
                              bool all_range_ticks_present) {
  if (inner_holds_within_range) {
    return PropertyResult::kPass;
  }
  if (strong) {
    return PropertyResult::kFail;
  }
  return all_range_ticks_present ? PropertyResult::kFail : PropertyResult::kPass;
}

PropertyResult EvalAbortAccept(bool abort_condition, PropertyResult inner) {
  // §16.12.14: a true abort condition forces the accept forms to true and takes
  // precedence over the underlying property_expr's verdict.
  if (abort_condition) return PropertyResult::kPass;
  return inner;
}

PropertyResult EvalAbortReject(bool abort_condition, PropertyResult inner) {
  // §16.12.14: a true abort condition forces the reject forms to false and takes
  // precedence over the underlying verdict. This is the dual of EvalAbortAccept:
  // reject_on(c) p is not(accept_on(c) not p), so a true condition that accepts
  // not(p) negates back to a fail, and a false condition leaves the underlying
  // verdict unchanged.
  if (abort_condition) return PropertyResult::kFail;
  return inner;
}

PropertyResult EvalNestedAbort(bool outer_forces_true, bool outer_condition,
                               bool inner_forces_true, bool inner_condition,
                               PropertyResult inner_property) {
  // §16.12.14: apply the inner abort operator first, then the outer one. Because
  // the outer operator forces its own outcome whenever its condition is true, it
  // overrides whatever the inner operator decided — so when both conditions
  // become true in the same time step the outermost operator takes precedence.
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
  // §16.13.2: evaluated as a property at a point, a multiclocked sequence is true
  // exactly when a match of the sequence begins at that point. The verdict is
  // definite — there is no pending reading at the multiclocked-property level.
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
  // §16.13.2: ticks are in increasing time order; the first that qualifies is the
  // nearest. The inclusive reading admits a tick coincident with `from`.
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
                                        consequent_clock_ticks, overlapping) ==
         antecedent_end_time;
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
  // §16.13.7: the evaluation attempt of a singly clocked instance always begins at
  // a tick of the single governing clock, and the initialization assignment is
  // performed at that beginning — so the init time is the attempt-begin time.
  return attempt_begin;
}

uint64_t MulticlockedLocalInitTick(
    uint64_t attempt_begin, const std::vector<uint64_t>& leading_clock_ticks) {
  // §16.13.7: schedule the init assignment at the earliest semantic-leading-clock
  // tick at or after the attempt begin. A tick coincident with the begin qualifies,
  // reusing the §16.13.2 at-or-after (inclusive) reading.
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
  // assignment is scheduled independently at the earliest tick of its own leading
  // clock at or after the attempt begin; that copy then governs the subproperty
  // associated with the same leading clock.
  std::vector<LocalVarInitCopy> copies;
  copies.reserve(per_leading_clock_ticks.size());
  for (size_t i = 0; i < per_leading_clock_ticks.size(); ++i) {
    copies.push_back(
        {i, MulticlockedLocalInitTick(attempt_begin, per_leading_clock_ticks[i])});
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
  bool witness = overlapping
                     ? left_nonvacuous_at_witness
                     : (left_nonvacuous_at_witness || right_nonvacuous_at_witness);
  return witness && !right_holds_at_prior_event && left_holds_at_all_prior_events;
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

PropertyResult EvalWeakSequenceProperty(bool finite_prefix_witnesses_inability) {
  // §16.12.2: the weak reading holds unless some finite prefix has already
  // ruled out any match.
  return finite_prefix_witnesses_inability ? PropertyResult::kFail
                                           : PropertyResult::kPass;
}

SequencePropertyStrength NegatePropertyStrength(SequencePropertyStrength inner) {
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

SampledValue SampleProceduralAssertionActionBlockArgument(uint64_t current_value) {
  return SampleProceduralAssertionArgument(current_value);
}

bool ActionBlockMayModifyArgument() {
  return false;
}

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

SampledValue SampleRecursiveExpression(
    SampledValue a, SampledValue b,
    uint64_t (*combinator)(uint64_t, uint64_t)) {

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

bool DisableConditionUsesCurrentValues() {
  return true;
}

bool DisableConditionAllowsTriggeredMethod() {
  return true;
}

bool DisableConditionAllowsMatchedMethod() {
  return false;
}

bool DisableConditionAllowsLocalVariableReference() {
  return false;
}

void ProceduralAssertionQueue::Enqueue(PendingProceduralAssertion pending) {

  pending.matured = false;
  queue_.push_back(std::move(pending));
}

void ProceduralAssertionQueue::MatureAll() {

  for (auto& p : queue_) p.matured = true;
}

void ProceduralAssertionQueue::Flush() {

  queue_.clear();
}

void ProceduralAssertionQueue::FlushPending() {
  std::erase_if(queue_, [](const PendingProceduralAssertion& p) {
    return !p.matured;
  });
}

void ProceduralAssertionQueue::FlushPendingForInstance(
    std::string_view instance_name) {
  std::erase_if(queue_, [&](const PendingProceduralAssertion& p) {
    return !p.matured && p.instance_name == instance_name;
  });
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

bool IsProceduralAssertionFlushPoint(FlushPointReason reason) {
  switch (reason) {
    case FlushPointReason::kEventControlResume:
    case FlushPointReason::kWaitResume:
    case FlushPointReason::kAlwaysCombSignalDelta:
    case FlushPointReason::kAlwaysLatchSignalDelta:
    case FlushPointReason::kDisableOuterScope:
      return true;
    case FlushPointReason::kNone:
      return false;
  }
  return false;
}

bool DisableFlushesProceduralAssertions(DisableTarget target) {
  switch (target) {
    case DisableTarget::kSpecificAssertion:
    case DisableTarget::kOutermostScope:
      return true;
    case DisableTarget::kNonOutermostScope:
    case DisableTarget::kTask:
      return false;
  }
  return false;
}

bool DisableFlushesDeferredAssertions(DisableTarget target) {
  switch (target) {
    case DisableTarget::kSpecificAssertion:
    case DisableTarget::kOutermostScope:
      return true;
    case DisableTarget::kNonOutermostScope:
    case DisableTarget::kTask:
      return false;
  }
  return false;
}

bool IsStaticConcurrentAssertion(bool appears_in_procedural_code) {

  return !appears_in_procedural_code;
}

bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic) {

  return !variable_is_automatic;
}

InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock,
    std::string_view default_clock) {

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

  return no_blocking_timing_control && exactly_one_event_control &&
         unique_qualifying_event_expr;
}

void MaturedAssertionQueue::Place(PendingProceduralAssertion matured) {

  matured.matured = true;
  queue_.push_back(std::move(matured));
}

std::vector<PendingProceduralAssertion> MaturedAssertionQueue::TakeAll() {
  return std::exchange(queue_, {});
}

uint32_t MaturedAssertionQueue::Size() const {
  return static_cast<uint32_t>(queue_.size());
}

void ExecuteDeferredAssertionAction(const DeferredAssertion& da) {
  if (da.condition_val != 0) {
    if (da.pass_action) da.pass_action();
  } else {
    if (da.fail_action) da.fail_action();
  }
}

bool UsesErrorSeverityFallback(const DeferredAssertion& da) {
  if (da.condition_val != 0) return false;
  if (da.kind == AssertionKind::kCover) return false;
  return !da.has_else_clause;
}

AssertActionBlockChoice SelectAssertActionBlock(bool property_passed,
                                                bool property_disabled) {
  if (property_disabled) return AssertActionBlockChoice::kNone;
  return property_passed ? AssertActionBlockChoice::kPass
                         : AssertActionBlockChoice::kFail;
}

AssertActionBlockChoice ResolveAssertActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled) {
  if (base == AssertActionBlockChoice::kPass && !pass_action_enabled) {
    return AssertActionBlockChoice::kNone;
  }
  if (base == AssertActionBlockChoice::kFail && !fail_action_enabled) {
    return AssertActionBlockChoice::kNone;
  }
  return base;
}

bool CallsDefaultErrorOnFailure(const DeferredAssertion& da,
                                bool fail_action_enabled) {
  return UsesErrorSeverityFallback(da) && fail_action_enabled;
}

AssertionSeverity DefaultConcurrentAssertActionSeverity() {
  return AssertionSeverity::kError;
}

Region ConcurrentAssertActionRegion() { return Region::kReactive; }

// §16.14.4: the same semantics as assume property — a restrict directs the tool
// to take its property as a constraint and prunes the state space identically.
bool RestrictSharesAssumeConstraintSemantics() { return true; }

// §16.14.4: a restrict property is not verified in simulation.
bool RestrictIsVerifiedInSimulation() { return false; }

// §16.14.4: a simulation cycle that violates the restriction is not an error,
// since the statement is never checked there.
bool RestrictViolationIsSimulationError() { return false; }

// §16.14.5: under `always` semantics a fresh evaluation attempt begins at every
// occurrence of the leading clock event, so over the run the number of attempts
// started equals the number of leading clock ticks.
int StaticConcurrentAssertionAttemptsStarted(int leading_clock_ticks) {
  return leading_clock_ticks;
}

// §16.14.5: the bare assert form and the explicit `always` assert form are
// equivalent.
bool StaticAssertEquivalentToAlwaysAssert() { return true; }

// §16.14.5: the bare cover form and the explicit `always` cover form are
// equivalent.
bool StaticCoverEquivalentToAlwaysCover() { return true; }

bool RoseGclk(uint64_t prev_lsb, uint64_t cur_lsb) {
  return (prev_lsb & 1u) == 0u && (cur_lsb & 1u) == 1u;
}

bool FellGclk(uint64_t prev_lsb, uint64_t cur_lsb) {
  return (prev_lsb & 1u) == 1u && (cur_lsb & 1u) == 0u;
}

bool StableGclk(uint64_t prev_value, uint64_t cur_value) {
  return prev_value == cur_value;
}

bool ChangedGclk(uint64_t prev_value, uint64_t cur_value) {
  return prev_value != cur_value;
}

bool RisingGclk(uint64_t cur_lsb, uint64_t next_lsb) {
  return (cur_lsb & 1u) == 0u && (next_lsb & 1u) == 1u;
}

bool FallingGclk(uint64_t cur_lsb, uint64_t next_lsb) {
  return (cur_lsb & 1u) == 1u && (next_lsb & 1u) == 0u;
}

bool SteadyGclk(uint64_t cur_value, uint64_t next_value) {
  return cur_value == next_value;
}

bool ChangingGclk(uint64_t cur_value, uint64_t next_value) {
  return !SteadyGclk(cur_value, next_value);
}

bool GclkFutureActionBlockDelayedToFollowingGlobalTick() { return true; }

bool GclkFutureKillAffectsAttempt(bool kill_at_or_before_last_assertion_tick) {
  return kill_at_or_before_last_assertion_tick;
}

bool ControlTypeAffectsStatistics(int control_type) {
  return control_type >= static_cast<int>(AssertControlType::kLock) &&
         control_type <= static_cast<int>(AssertControlType::kKill);
}

bool ControlAffectsAssertionType(uint32_t assertion_type_mask,
                                 AssertionTypeBit bit) {
  return (assertion_type_mask & static_cast<uint32_t>(bit)) != 0;
}

bool ControlAffectsDirectiveType(uint32_t directive_type_mask,
                                 DirectiveTypeBit bit) {
  return (directive_type_mask & static_cast<uint32_t>(bit)) != 0;
}

bool EquivalentAssertControlForTask(std::string_view task_name,
                                    AssertControlInvocation& out) {
  // §20.11: $asserton/$assertoff/$assertkill use assertion_type 15; the action
  // control tasks use assertion_type 31. Both families use directive_type 7.
  constexpr uint32_t kStatusAssertionType = 15;
  constexpr uint32_t kActionAssertionType = 31;
  constexpr uint32_t kDirective = 7;
  auto set = [&](uint32_t control_type, uint32_t assertion_type) {
    out.control_type = control_type;
    out.assertion_type = assertion_type;
    out.directive_type = kDirective;
    return true;
  };
  if (task_name == "$asserton") {
    return set(static_cast<uint32_t>(AssertControlType::kOn),
               kStatusAssertionType);
  }
  if (task_name == "$assertoff") {
    return set(static_cast<uint32_t>(AssertControlType::kOff),
               kStatusAssertionType);
  }
  if (task_name == "$assertkill") {
    return set(static_cast<uint32_t>(AssertControlType::kKill),
               kStatusAssertionType);
  }
  if (task_name == "$assertpasson") {
    return set(static_cast<uint32_t>(AssertControlType::kPassOn),
               kActionAssertionType);
  }
  if (task_name == "$assertpassoff") {
    return set(static_cast<uint32_t>(AssertControlType::kPassOff),
               kActionAssertionType);
  }
  if (task_name == "$assertfailon") {
    return set(static_cast<uint32_t>(AssertControlType::kFailOn),
               kActionAssertionType);
  }
  if (task_name == "$assertfailoff") {
    return set(static_cast<uint32_t>(AssertControlType::kFailOff),
               kActionAssertionType);
  }
  if (task_name == "$assertnonvacuouson") {
    return set(static_cast<uint32_t>(AssertControlType::kNonvacuousOn),
               kActionAssertionType);
  }
  if (task_name == "$assertvacuousoff") {
    return set(static_cast<uint32_t>(AssertControlType::kVacuousOff),
               kActionAssertionType);
  }
  return false;
}

bool IsDeferredFlushPoint(FlushPointReason reason) {
  switch (reason) {
    case FlushPointReason::kEventControlResume:
    case FlushPointReason::kWaitResume:
    case FlushPointReason::kAlwaysCombSignalDelta:
    case FlushPointReason::kAlwaysLatchSignalDelta:
    case FlushPointReason::kDisableOuterScope:
      return true;
    case FlushPointReason::kNone:
      return false;
  }
  return false;
}

void DeferredReportQueue::Enqueue(PendingDeferredReport report) {
  report.matured = false;
  entries_.push_back(std::move(report));
}

void DeferredReportQueue::MatureObservedReports() {
  for (auto& e : entries_) {
    if (e.deferral == DeferralKind::kObserved) e.matured = true;
  }
}

void DeferredReportQueue::MatureFinalReports() {
  for (auto& e : entries_) {
    if (e.deferral == DeferralKind::kFinal) e.matured = true;
  }
}

std::vector<PendingDeferredReport> DeferredReportQueue::TakeMaturedObserved() {
  std::vector<PendingDeferredReport> taken;
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured && e.deferral == DeferralKind::kObserved) {
      taken.push_back(std::move(e));
    } else {
      kept.push_back(std::move(e));
    }
  }
  entries_ = std::move(kept);
  return taken;
}

std::vector<PendingDeferredReport> DeferredReportQueue::TakeMaturedFinal() {
  std::vector<PendingDeferredReport> taken;
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured && e.deferral == DeferralKind::kFinal) {
      taken.push_back(std::move(e));
    } else {
      kept.push_back(std::move(e));
    }
  }
  entries_ = std::move(kept);
  return taken;
}

void DeferredReportQueue::FlushNonMatured() {
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured) kept.push_back(std::move(e));
  }
  entries_ = std::move(kept);
}

void DeferredReportQueue::FlushNonMaturedForInstance(
    std::string_view instance_name) {
  std::erase_if(entries_, [&](const PendingDeferredReport& e) {
    return !e.matured && e.da.instance_name == instance_name;
  });
}

uint32_t DeferredReportQueue::Size() const {
  return static_cast<uint32_t>(entries_.size());
}

uint32_t DeferredReportQueue::MaturedCount() const {
  uint32_t n = 0;
  for (const auto& e : entries_) {
    if (e.matured) ++n;
  }
  return n;
}

uint32_t DeferredReportQueue::NonMaturedCount() const {
  return Size() - MaturedCount();
}

bool AssertionControl::IsEnabled(std::string_view inst) const {
  if (global_off_) return false;
  return disabled_.find(std::string(inst)) == disabled_.end() &&
         killed_.find(std::string(inst)) == killed_.end();
}

void AssertionControl::SetOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  disabled_.insert(std::string(inst));
}

void AssertionControl::SetOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  disabled_.erase(std::string(inst));
}

void AssertionControl::Kill(std::string_view inst) {
  if (IsLocked(inst)) return;
  killed_.insert(std::string(inst));
  disabled_.insert(std::string(inst));
}

bool AssertionControl::WasKilled(std::string_view inst) const {
  return killed_.find(std::string(inst)) != killed_.end();
}

void AssertionControl::SetGlobalOff() { global_off_ = true; }

void AssertionControl::SetGlobalOn() { global_off_ = false; }

void AssertionControl::Lock(std::string_view inst) {
  locked_.insert(std::string(inst));
}

void AssertionControl::Unlock(std::string_view inst) {
  locked_.erase(std::string(inst));
}

bool AssertionControl::IsLocked(std::string_view inst) const {
  return locked_.find(std::string(inst)) != locked_.end();
}

bool AssertionControl::IsPassEnabled(std::string_view inst) const {
  return IsVacuousPassEnabled(inst) && IsNonvacuousPassEnabled(inst);
}

void AssertionControl::SetPassOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.insert(std::string(inst));
  nonvacuous_pass_off_.insert(std::string(inst));
}

void AssertionControl::SetPassOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.erase(std::string(inst));
  nonvacuous_pass_off_.erase(std::string(inst));
}

bool AssertionControl::IsVacuousPassEnabled(std::string_view inst) const {
  return vacuous_pass_off_.find(std::string(inst)) == vacuous_pass_off_.end();
}

bool AssertionControl::IsNonvacuousPassEnabled(std::string_view inst) const {
  return nonvacuous_pass_off_.find(std::string(inst)) ==
         nonvacuous_pass_off_.end();
}

void AssertionControl::SetNonvacuousOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  nonvacuous_pass_off_.erase(std::string(inst));
}

void AssertionControl::SetVacuousOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.insert(std::string(inst));
}

bool AssertionControl::IsFailEnabled(std::string_view inst) const {
  return fail_off_.find(std::string(inst)) == fail_off_.end();
}

void AssertionControl::SetFailOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  fail_off_.insert(std::string(inst));
}

void AssertionControl::SetFailOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  fail_off_.erase(std::string(inst));
}

void AssertionControl::ApplyControl(int control_type, std::string_view inst) {
  // §20.11: Unlock is the only control that reaches a locked assertion; every
  // other control_type is a no-op while the assertion is locked.
  if (control_type == static_cast<int>(AssertControlType::kUnlock)) {
    Unlock(inst);
    return;
  }
  if (IsLocked(inst)) return;
  switch (static_cast<AssertControlType>(control_type)) {
    case AssertControlType::kLock:
      Lock(inst);
      break;
    case AssertControlType::kUnlock:
      Unlock(inst);
      break;
    case AssertControlType::kOn:
      SetOn(inst);
      break;
    case AssertControlType::kOff:
      SetOff(inst);
      break;
    case AssertControlType::kKill:
      Kill(inst);
      break;
    case AssertControlType::kPassOn:
      SetPassOn(inst);
      break;
    case AssertControlType::kPassOff:
      SetPassOff(inst);
      break;
    case AssertControlType::kFailOn:
      SetFailOn(inst);
      break;
    case AssertControlType::kFailOff:
      SetFailOff(inst);
      break;
    case AssertControlType::kNonvacuousOn:
      SetNonvacuousOn(inst);
      break;
    case AssertControlType::kVacuousOff:
      SetVacuousOff(inst);
      break;
  }
}

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

  return procedural_queues_[std::string(process_id)];
}

DeferredReportQueue& SvaEngine::GetDeferredReportQueue(
    std::string_view process_id) {
  return per_process_reports_[std::string(process_id)];
}

const DeferredReportQueue* SvaEngine::PeekDeferredReportQueue(
    std::string_view process_id) const {
  auto it = per_process_reports_.find(std::string(process_id));
  if (it == per_process_reports_.end()) return nullptr;
  return &it->second;
}

void SvaEngine::QueuePendingReport(std::string_view process_id,
                                   const DeferredAssertion& da,
                                   DeferralKind kind) {
  PendingDeferredReport report;
  report.process_id = std::string(process_id);
  report.deferral = kind;
  report.da = da;
  GetDeferredReportQueue(process_id).Enqueue(std::move(report));
}

void SvaEngine::MatureObservedReports(std::string_view process_id) {
  GetDeferredReportQueue(process_id).MatureObservedReports();
}

void SvaEngine::MatureFinalReports(std::string_view process_id) {
  GetDeferredReportQueue(process_id).MatureFinalReports();
}

uint32_t SvaEngine::ExecuteMaturedObservedInReactive(
    std::string_view process_id, Scheduler& sched, SimTime time) {
  auto matured = GetDeferredReportQueue(process_id).TakeMaturedObserved();
  for (auto& report : matured) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(report.da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kReactive, event);
  }
  return static_cast<uint32_t>(matured.size());
}

uint32_t SvaEngine::ExecuteMaturedFinalInPostponed(
    std::string_view process_id, Scheduler& sched, SimTime time) {
  auto matured = GetDeferredReportQueue(process_id).TakeMaturedFinal();
  for (auto& report : matured) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(report.da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kPostponed, event);
  }
  return static_cast<uint32_t>(matured.size());
}

void SvaEngine::OnDeferredFlushPoint(std::string_view process_id,
                                     FlushPointReason reason) {
  if (!IsDeferredFlushPoint(reason)) return;
  GetDeferredReportQueue(process_id).FlushNonMatured();
}

void SvaEngine::OnProceduralAssertionFlushPoint(std::string_view process_id,
                                                FlushPointReason reason) {
  if (!IsProceduralAssertionFlushPoint(reason)) return;
  GetProceduralQueue(process_id).FlushPending();
}

void SvaEngine::ApplyDisableToProceduralAssertions(
    std::string_view process_id, DisableTarget target,
    std::string_view assertion_instance) {
  if (!DisableFlushesProceduralAssertions(target)) return;
  if (target == DisableTarget::kSpecificAssertion) {
    GetProceduralQueue(process_id).FlushPendingForInstance(assertion_instance);
  } else {
    GetProceduralQueue(process_id).FlushPending();
  }
}

void SvaEngine::ApplyDisableToDeferredAssertions(
    std::string_view process_id, DisableTarget target,
    std::string_view assertion_instance) {
  if (!DisableFlushesDeferredAssertions(target)) return;
  if (target == DisableTarget::kSpecificAssertion) {
    GetDeferredReportQueue(process_id).FlushNonMaturedForInstance(
        assertion_instance);
  } else {
    GetDeferredReportQueue(process_id).FlushNonMatured();
  }
}

ExpectActionKind ResolveExpectAction(PropertyResult result,
                                     bool has_else_clause) {
  // §16.17: a pending property keeps the process blocked; a resolved property
  // selects which arm of the action block runs.
  switch (result) {
    case PropertyResult::kPending:
      return ExpectActionKind::kBlock;
    case PropertyResult::kPass:
    case PropertyResult::kVacuousPass:
      return ExpectActionKind::kRunPass;
    case PropertyResult::kFail:
      return has_else_clause ? ExpectActionKind::kRunFail
                             : ExpectActionKind::kReportError;
  }
  return ExpectActionKind::kBlock;
}

bool ExpectProcessRemainsBlocked(PropertyResult result) {
  // §16.17: the process unblocks only once the property succeeds or fails.
  return result == PropertyResult::kPending;
}

bool ExpectClockingEventBeginsEvaluation(uint64_t activation_tick,
                                         uint64_t clocking_event_tick) {
  // §16.17: the first evaluation is on the next clocking event after the expect
  // executes, not on one coincident with activation.
  return clocking_event_tick > activation_tick;
}

}
