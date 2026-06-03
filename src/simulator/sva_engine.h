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

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

std::string_view SeverityToString(AssertionSeverity sev);

enum class PropertyResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
  kPending,
};

struct SequenceAttempt {
  uint32_t position = 0;
  uint32_t delay_remaining = 0;
  uint32_t match_count = 0;
  bool completed = false;
  bool failed = false;
};

void AdvanceSequence(SequenceAttempt& sa);

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

bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

// §16.9.2.1: an empty sequence match (e.g. a[*0]) spans zero clock ticks and is
// thus of length 0, so concatenating it with another sequence through the
// ##delay operator obeys a dedicated set of rules. Which operand of the
// concatenation is the empty match.
enum class EmptyConcatSide : uint8_t { kEmptyLeft, kEmptyRight };

// Outcome of concatenating an empty match with another sequence via ##n.
struct EmptyConcatResult {
  // false records that "(empty ##0 seq)" and "(seq ##0 empty)" do not result in
  // a match; true means the concatenation collapses onto the surviving operand.
  bool matchable = false;
  // The ##(n-1) delay carried onto the surviving operand. Because the empty
  // operand occupies zero ticks, concatenating across it spends one tick fewer
  // than the written delay — the same reason an empty case (a[*0]) runs one tick
  // shorter than the corresponding length-1 case (a[*1]).
  uint32_t effective_delay = 0;
  // "(seq ##n empty)" trails the surviving sequence with `true, extending the
  // match one tick past seq's end; the empty-on-the-left rule does not.
  bool append_true = false;
};

EmptyConcatResult ConcatEmptyMatch(EmptyConcatSide side, uint32_t delay);

// §16.9.2.1: a sequence admitting both empty and nonempty matches — a repetition
// whose count range spans zero, e.g. a[*0:1] — is evaluated by rewriting it as
// the OR of its empty case (count 0) and its nonempty cases (count >= 1). The
// composite matches when either disjunct matches; a range that excludes zero has
// only the nonempty case.
bool MatchEmptyOrNonempty(uint32_t rep_min, bool empty_case_match,
                          bool nonempty_case_match);

bool EvalSequenceAnd(bool a_match, bool b_match);

// §16.9.5: the composite `e1 and e2` requires both operands to match. The
// operands begin at the same time, but their matches can complete at different
// times; once one operand matches it waits for the other, so the composite
// match completes at the later of the two operand end times. This carries the
// end-time alongside the match decision that EvalSequenceAnd reports.
struct SequenceAndMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time);

bool EvalSequenceOr(bool a_match, bool b_match);
bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

// §16.9.10: the containment `seq1 within seq2` is an abbreviation for
// (1[*0:$] ##1 seq1 ##1 1[*0:$]) intersect seq2. The composite matches along a
// finite interval of consecutive clock ticks when seq2 matches along the whole
// interval and seq1 matches along some subinterval of it. Both operands shall
// therefore match, and the match of seq1 shall be contained in the match of
// seq2: seq1 shall start no earlier than seq2 starts and shall complete no later
// than seq2 completes. The intersection forces the composite to span seq2's
// interval, so the containment completes at seq2's match point. This carries the
// composite end-time alongside the match decision.
struct SequenceWithinMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceWithinMatch EvalSequenceWithin(bool inner_match, uint32_t inner_start,
                                       uint32_t inner_end, bool outer_match,
                                       uint32_t outer_start, uint32_t outer_end);

// §16.12.7: an implication `sequence_expr |-> property_expr` (overlapped) or
// `sequence_expr |=> property_expr` (nonoverlapped) preconditions the consequent
// property_expr on a match of the antecedent sequence_expr. When the antecedent
// has no match the implication holds vacuously. The overlapped form evaluates
// the consequent at the end point of the match, so the result is the
// consequent's verdict; the nonoverlapped form starts the consequent one clock
// tick later, so its verdict is deferred (kPending) and settled by
// ResolveNonOverlapping — capturing `seq |=> p` ≡ `seq ##1 `true |-> p`.
PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping);

// §16.12.3: a negation `not property_expr` returns the opposite verdict of the
// underlying property_expr — a true underlying evaluation makes the negation
// false, and a false one makes it true. Each attempt of the negation drives a
// single attempt of the underlying property_expr.
PropertyResult EvalPropertyNot(PropertyResult inner);
PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);

// §16.12.4: a disjunction `property_expr1 or property_expr2` evaluates to true
// if, and only if, at least one of the two operand property expressions
// evaluates to true. A vacuous pass counts as the operand holding, so a single
// holding operand is enough to make the whole disjunction hold.
PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);

// §16.12.6: an if-else property is governed by the guard expression. When the
// guard holds, the overall result is that of the then-branch. The single-branch
// form (no else) holds vacuously when the guard is false, since there is nothing
// to check; the two-branch form routes a false guard to the else-branch instead.
PropertyResult EvalPropertyIfElse(bool cond, PropertyResult then_result,
                                  bool has_else, PropertyResult else_result);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);

// §16.12.7: settles a deferred nonoverlapped (|=>) implication once the clock
// reaches the tick after the antecedent match, where the consequent is finally
// evaluated.
PropertyResult ResolveNonOverlapping(bool consequent_matched);

// §16.12.8: a property `property_expr1 implies property_expr2` evaluates to true
// if, and only if, the antecedent fails to hold or the consequent holds — the
// ordinary logical implication over the two operands' verdicts. Unlike the
// sequence implication operators of §16.12.7 there is no antecedent match point
// to defer to, so the result settles from the operand verdicts directly. A
// vacuous pass counts as the operand holding, mirroring EvalPropertyOr.
PropertyResult EvalPropertyImplies(PropertyResult antecedent,
                                   PropertyResult consequent);

// §16.12.8: a property `property_expr1 iff property_expr2` evaluates to true if,
// and only if, both operands hold or both operands fail to hold — the operands'
// verdicts must agree. A vacuous pass counts as the operand holding.
PropertyResult EvalPropertyIff(PropertyResult a, PropertyResult b);

// §16.12.9: a followed-by `sequence_expr #-# property_expr` (overlapped) or
// `sequence_expr #=# property_expr` (nonoverlapped) triggers monitoring of the
// consequent property_expr at a match point of the antecedent sequence_expr.
// For the followed-by to succeed the antecedent shall have at least one match
// and the consequent shall hold from a match point; unlike implication a
// missing match is a definite fail, never a vacuous pass, so the result is
// always plainly true or false. The followed-by operators are the duals of the
// implication operators — `s #-# p` ≡ not (s |-> not p) and
// `s #=# p` ≡ not (s |=> not p) — equivalently `s #-# p` is strong(s ##0 ...)
// and `s #=# p` is strong(s ##1 ...). The verdict is therefore obtained by
// negating the consequent, running the matching §16.12.7 implication, and
// negating its verdict. The overlapped form evaluates the consequent at the end
// point of the match so it settles immediately; the nonoverlapped form starts
// the consequent one tick later, so the verdict is deferred (kPending) and
// settled by ResolveFollowedByNonOverlapping.
PropertyResult EvalFollowedBy(bool antecedent, bool consequent,
                              bool non_overlapping);

// §16.12.9: settles a deferred nonoverlapped followed-by (#=#) at the tick after
// the antecedent match, where the consequent property_expr is finally
// evaluated. By the duality with |=>, the dual implication settles on the
// negated consequent and that verdict is negated, so a holding consequent makes
// the followed-by pass.
PropertyResult ResolveFollowedByNonOverlapping(bool consequent_matched);

// §16.12.10: the nexttime property operators advance evaluation to a later tick
// of the property's clock. `nexttime property_expr` (weak) holds when the
// property_expr holds at the next clock tick or there is no further clock tick;
// `s_nexttime property_expr` (strong) requires the next clock tick to exist and
// the property_expr to hold there. The indexed forms `nexttime[n]` and
// `s_nexttime[n]` target the n-th future tick instead of the immediately next
// one. The only difference between the weak and strong readings is how an
// unreachable target tick is judged: weakly it passes (the clock ran out before
// the obligation could be disproven), strongly it fails (the required tick never
// arrived). When the target tick is reachable the nexttime verdict is exactly
// the property_expr's verdict at that tick.
PropertyResult EvalNexttime(bool strong, bool target_tick_reachable,
                            PropertyResult inner_at_target);

// §16.12.10: decide whether the indexed target tick is reachable. The index
// counts ticks of the nexttime property's clock with counting starting at the
// current time step, so reaching the target for index `n` requires `n` further
// ticks after the current step. Consequently `nexttime[0]`/`s_nexttime[0]`
// target the current step and act as pure alignment operators, while the
// non-indexed nexttime/s_nexttime correspond to index 1 (the next tick).
bool NexttimeTargetReachable(uint64_t index, uint64_t future_clock_ticks);

// §16.12.11: sentinel maximum for an unbounded weak always range. A weak always
// range may be unbounded; the strong form's range is always bounded.
inline constexpr int kAlwaysUnboundedMax = -1;

// §16.12.11: outcome of an `always`/`s_always` property over its window of clock
// ticks. `strong` selects `s_always` (strong) versus `always` (weak).
// `all_covered_ticks_present` says whether every clock tick the range demands is
// actually present; only the strong form requires the covered ticks to exist,
// since for a weak always it is not required that all clock ticks within the
// range exist. `inner_holds_at_present_ticks` says whether the inner
// property_expr held at every covered tick that is present.
//
// The weak form holds when the inner property_expr held at every present tick,
// regardless of whether some covered ticks are missing. The strong form holds
// only when every covered tick exists and the inner property_expr held at each.
PropertyResult EvalAlways(bool strong, bool all_covered_ticks_present,
                          bool inner_holds_at_present_ticks);

// §16.12.11: whether the clock tick at `index` (counted from the current time
// step, so index 0 is the current step) lies within an always range whose
// inclusive bounds are [`range_min`, `range_max`]. The non-ranged weak always
// covers every current or future tick, modelled as `range_min == 0` with an
// unbounded maximum. `range_max == kAlwaysUnboundedMax` denotes an unbounded
// maximum, which covers every tick from `range_min` onward.
bool AlwaysRangeCovers(int index, int range_min, int range_max);

// §16.12.11: for a strong always, every clock tick the range covers shall exist.
// Counting starts at the current time step, so the covered ticks all exist when
// at least `range_max` further ticks are available after the current step.
bool AlwaysStrongTicksAllPresent(int range_max, int future_clock_ticks);

// §16.12.12: sentinel for the offset of the first tick at which the right
// operand of an until property holds, used when it never holds at any current
// or future clock tick.
inline constexpr int kUntilRhsNever = -1;

// §16.12.12: whether the left operand holds at every clock tick it is required
// to for an until property. `lhs_run_length` is the number of consecutive ticks,
// starting at the evaluation attempt, at which the left operand holds.
// `first_rhs_index` is the offset of the first tick at which the right operand
// holds (kUntilRhsNever when it never holds). For the non-overlapping forms
// (until / s_until) the left operand is required only on the ticks before the
// first right-operand tick; for the overlapping forms (until_with /
// s_until_with) it is also required at that tick. When the right operand never
// holds, the left operand is required at every tick of the trace, whose length
// is `trace_length`.
bool UntilLeftHoldsRequired(bool overlapping, int lhs_run_length,
                            int first_rhs_index, int trace_length);

// §16.12.12: verdict for the four until property forms given that the left
// operand held at every required tick (`lhs_holds_required`) and whether the
// right operand holds at some current or future tick (`rhs_holds_eventually`).
// The strong forms (s_until / s_until_with) require the right operand to hold;
// the weak forms (until / until_with) hold even if it never does.
PropertyResult EvalUntil(bool strong, bool rhs_holds_eventually,
                         bool lhs_holds_required);

// §16.12.13: verdict for the eventually property forms. `s_eventually` (with or
// without a range) is the strong form and the ranged `eventually` is the weak
// form; the non-ranged strong form covers every current or future clock tick.
// `inner_holds_within_range` is whether the inner property_expr holds at some
// present clock tick within the range. `all_range_ticks_present` is whether every
// clock tick the range covers exists. The strong form requires such a witness and
// fails when none is found; the weak form also holds when the range's ticks do
// not all exist, since it does not require those later ticks to be present.
PropertyResult EvalEventually(bool strong, bool inner_holds_within_range,
                              bool all_range_ticks_present);

// §16.12.14: an accept abort property (accept_on / sync_accept_on) evaluates the
// underlying property_expr, but if the abort condition becomes true during that
// evaluation the overall result is forced to true; otherwise the result is the
// underlying verdict. The abort condition takes precedence, so a true condition
// wins even over an underlying verdict that has already settled.
PropertyResult EvalAbortAccept(bool abort_condition, PropertyResult inner);

// §16.12.14: a reject abort property (reject_on / sync_reject_on) forces the
// overall result to false when the abort condition becomes true; otherwise the
// result is the underlying verdict. The standard defines reject_on(c) p as
// not(accept_on(c) not p), and likewise for the synchronous form.
PropertyResult EvalAbortReject(bool abort_condition, PropertyResult inner);

// §16.12.14: nested abort operators are evaluated in lexical order, outermost
// first. When the conditions of two nested abort operators become true in the
// same time step during evaluation of the argument property, the outermost
// operator takes precedence and decides the verdict. The `_forces_true` flags
// select accept (true) versus reject (false) polarity for each operator.
PropertyResult EvalNestedAbort(bool outer_forces_true, bool outer_condition,
                               bool inner_forces_true, bool inner_condition,
                               PropertyResult inner_property);

// §16.12.14: the abort condition is evaluated using the sampled value as a
// regular Boolean expression — unlike `disable iff`, whose condition uses
// current values (see DisableConditionUsesCurrentValues).
bool AbortConditionUsesSampledValues();

// §16.12.14: the asynchronous abort operators (accept_on, reject_on) are
// evaluated at the granularity of every simulation time step, like disable iff;
// the synchronous operators (sync_accept_on, sync_reject_on) are evaluated only
// at the simulation time step when the clocking event happens.
bool AbortConditionEvaluatedAtClockingEventOnly(bool synchronous_abort);

// §16.13.2: a multiclocked sequence is itself a multiclocked property. When a
// multiclocked sequence is evaluated as a property beginning at some point, the
// evaluation is true if, and only if, there is a match of the sequence beginning
// at that point. Like a singly clocked property the result is always a definite
// true or false, never pending.
PropertyResult EvalMulticlockedSequenceAsProperty(bool sequence_has_match);

// §16.13.2: a Boolean `and` whose two operands are clocked by different clocks
// forms a multiclocked property — but not a multiclocked sequence. Both operands
// begin at the same evaluation point, each on its own clock; the conjunction is
// true if, and only if, both operands have a match beginning at that point.
PropertyResult EvalMulticlockedAnd(bool left_operand_has_match,
                                   bool right_operand_has_match);

// §16.13.2: sentinel returned when no tick of the relevant clock is available to
// locate the evaluation point of a multiclocked operand.
inline constexpr uint64_t kNoMulticlockTick = ~static_cast<uint64_t>(0);

// §16.13.2: the nearest tick of `clock_ticks` at which a multiclocked operand is
// evaluated relative to time `from`. When `inclusive` is true a tick coincident
// with `from` qualifies (the "possibly overlapping" / "non-strictly subsequent"
// reading); when false only strictly future ticks qualify. `clock_ticks` shall
// be in increasing time order. Returns kNoMulticlockTick when no qualifying tick
// exists.
uint64_t NearestClockTickAtOrAfter(uint64_t from,
                                   const std::vector<uint64_t>& clock_ticks,
                                   bool inclusive);

// §16.13.2: the tick at which the consequent of a multiclocked implication is
// evaluated. Both forms synchronize from the antecedent match end time to a tick
// of the consequent's clock. The nonoverlapping form (|=>) advances to the
// nearest strictly future consequent-clock tick. The overlapping form (|->)
// awaits the nearest consequent-clock tick: when the consequent clock ticks at
// the antecedent end the consequent is checked there immediately, otherwise it
// behaves as the nonoverlapping form. Returns kNoMulticlockTick when no
// qualifying consequent-clock tick exists.
uint64_t MulticlockedConsequentEvalTick(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

// §16.13.2: whether a multiclocked overlapping implication (|->) checks its
// consequent immediately, i.e. the consequent clock ticks at the antecedent match
// end. The nonoverlapping form (|=>) never checks immediately because it advances
// to a strictly future tick.
bool MulticlockedImplicationChecksImmediately(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

// §16.13.2: the tick at which a branch of a multiclocked if / if-else property is
// evaluated. The condition is checked at the property clock (`condition_time`);
// the then-branch is then evaluated at the nearest, possibly overlapping tick of
// its clock and the else-branch at the nearest non-strictly subsequent tick of
// its clock. Both readings admit a tick coincident with the condition check, so
// the branch tick is the nearest tick at or after `condition_time`. Returns
// kNoMulticlockTick when the branch clock has no qualifying tick.
uint64_t MulticlockedIfBranchEvalTick(
    uint64_t condition_time, const std::vector<uint64_t>& branch_clock_ticks);

// §16.14.8: nonvacuous evaluation. Every evaluation attempt of a property is
// either vacuous or nonvacuous, and nonvacuity is defined recursively on the
// structure of the property. The helpers below compute that attribute for one
// property form from the nonvacuity of its subproperty attempts together with
// the runtime facts each form depends on (whether a guard holds, whether an
// antecedent matched, and so on). Nonvacuity is independent of the pass/fail
// verdict: a failing attempt can still be nonvacuous. The companion rule, that
// an attempt succeeds nonvacuously exactly when the property evaluates to true
// and the attempt is nonvacuous, is PropertySucceedsNonvacuously.

// §16.14.8(a)(b)(c): an attempt of a property that is a bare sequence_expr, or
// of strong(sequence_expr) or weak(sequence_expr), is always nonvacuous.
bool NonvacuousSequenceForm();

// §16.14.8(d)(i): the attempt of `not property_expr`, or of an instance of a
// property obtained by substituting actual arguments for the formal arguments,
// is nonvacuous exactly when its single underlying subproperty attempt is.
bool NonvacuousPassthrough(bool inner_nonvacuous);

// §16.14.8(e)(f)(aa): the attempt of `property_expr1 or property_expr2`,
// `property_expr1 and property_expr2`, or `property_expr1 iff property_expr2`
// is nonvacuous when either operand's underlying attempt is nonvacuous.
bool NonvacuousDisjunctiveForm(bool left_nonvacuous, bool right_nonvacuous);

// §16.14.8(g): the attempt of `if (expression_or_dist) property_expr1` is
// nonvacuous when the guard holds and the then-branch attempt is nonvacuous.
// With an else branch a false guard instead routes to the else-branch attempt,
// so the attempt is nonvacuous when that branch is reached and is nonvacuous;
// the single-branch form with a false guard holds vacuously.
bool NonvacuousIfElse(bool guard_holds, bool then_nonvacuous, bool has_else,
                      bool else_nonvacuous);

// §16.14.8(h)(j)(k): the attempt of a sequence-preconditioned property — the
// implications `sequence_expr |-> property_expr` and `sequence_expr |=>
// property_expr`, and the followed-by forms `sequence_expr #-# property_expr`
// and `sequence_expr #=# property_expr` — is nonvacuous when the antecedent
// sequence has a match point and the consequent attempt that starts from that
// point is nonvacuous. The overlapped forms (|->, #-#) start the consequent at
// the antecedent end point; the nonoverlapped forms (|=>, #=#) start it at the
// following clock event. Either way nonvacuity requires an antecedent match and
// a nonvacuous consequent attempt.
bool NonvacuousSequencePrecondition(bool antecedent_has_match,
                                    bool consequent_nonvacuous);

// §16.14.8(l)(m)(n)(o): the attempt of a nexttime/s_nexttime property, indexed
// or not, is nonvacuous when the targeted future clock event is reachable and
// the subproperty attempt that begins there is nonvacuous. Nonvacuity does not
// distinguish the weak (nexttime) from the strong (s_nexttime) reading.
bool NonvacuousNexttime(bool target_clock_event_reachable,
                        bool inner_nonvacuous_at_target);

// §16.14.8(p)(q)(r): the attempt of an always/s_always property, ranged or not,
// is nonvacuous when there is a covered clock event at which the subproperty
// attempt is nonvacuous and the subproperty does not fail at any earlier
// covered clock event.
bool NonvacuousAlways(bool inner_nonvacuous_at_some_covered_event,
                      bool inner_fails_at_prior_covered_event);

// §16.14.8(s)(t)(u): the attempt of an s_eventually/eventually property, ranged
// or not, is nonvacuous when there is a covered clock event at which the
// subproperty attempt is nonvacuous and the subproperty does not hold at any
// earlier covered clock event.
bool NonvacuousEventually(bool inner_nonvacuous_at_some_covered_event,
                          bool inner_holds_at_prior_covered_event);

// §16.14.8(v)(w)(x)(y): the attempt of an until-family property is nonvacuous
// when, at some clock event, a witnessing subproperty attempt is nonvacuous,
// the right operand does not hold at any earlier clock event, and the left
// operand holds at every earlier clock event. For the non-overlapping forms
// (until, s_until) the witness is either operand's attempt being nonvacuous; for
// the overlapping forms (until_with, s_until_with) only the left operand's
// attempt witnesses. Nonvacuity does not distinguish the weak from the strong
// reading.
bool NonvacuousUntil(bool overlapping, bool left_nonvacuous_at_witness,
                     bool right_nonvacuous_at_witness,
                     bool right_holds_at_prior_event,
                     bool left_holds_at_all_prior_events);

// §16.14.8(z): the attempt of `property_expr1 implies property_expr2` is
// nonvacuous when the antecedent attempt is true and nonvacuous and the
// consequent attempt is nonvacuous.
bool NonvacuousImplies(bool antecedent_true, bool antecedent_nonvacuous,
                       bool consequent_nonvacuous);

// §16.14.8(ab)(ac)(ad)(ae)(ag): the attempt of an abort property (accept_on,
// reject_on, sync_accept_on, sync_reject_on) or of `disable iff
// (expression_or_dist) property_expr` is nonvacuous when the underlying
// subproperty attempt is nonvacuous and the abort/disable condition does not
// hold at any evaluated step of that attempt. The asynchronous abort forms and
// the disable form evaluate the condition at every time step; the synchronous
// abort forms evaluate it only at clock events — but in every case nonvacuity
// requires the condition never to hold across the evaluated steps.
bool NonvacuousAbortOrDisable(bool inner_nonvacuous,
                             bool condition_holds_at_any_evaluated_step);

// §16.14.8(af): the attempt of a `case` property is nonvacuous when one case
// item is selected — a matching expression_or_dist, or the default when no item
// matches — and that selected item's property_stmt attempt is nonvacuous.
bool NonvacuousCase(bool a_branch_selected, bool selected_stmt_nonvacuous);

// §16.14.8: an evaluation attempt of a property succeeds nonvacuously exactly
// when the property evaluates to true and the attempt is nonvacuous.
bool PropertySucceedsNonvacuously(bool property_true, bool attempt_nonvacuous);

enum class AssertionKind : uint8_t {
  kAssert = 0,
  kAssume = 1,
  kCover = 2,
  kRestrict = 3,
};

// §16.12.2: a sequence property has one of three forms — a bare sequence_expr,
// weak(sequence_expr), or strong(sequence_expr). strong and weak are the
// sequence operators that fix the evaluation strength; when neither appears the
// strength is inferred from the enclosing assertion statement.
enum class SequencePropertyStrength : uint8_t {
  kWeak = 0,
  kStrong = 1,
};

// §16.12.2: when the strong/weak operator is omitted, a bare sequence_expr is
// evaluated weakly inside assert property and assume property, and strongly
// inside every other assertion statement (e.g. cover property, restrict
// property).
SequencePropertyStrength DefaultSequencePropertyStrength(AssertionKind stmt);

// §16.12.2: strong(sequence_expr) is true if, and only if, there is a nonempty
// match of the sequence_expr. One match suffices, so this also gives
// strong(first_match(sequence_expr)).
PropertyResult EvalStrongSequenceProperty(bool has_nonempty_match);

// §16.12.2: weak(sequence_expr) is true if, and only if, no finite prefix
// witnesses inability to match the sequence_expr. A prefix witnesses inability
// for sequence_expr exactly when it does for first_match(sequence_expr), so
// this also gives weak(first_match(sequence_expr)).
PropertyResult EvalWeakSequenceProperty(bool finite_prefix_witnesses_inability);

// §16.12.3: the `not` operator switches the strength of the property it
// negates. Negating a weak property yields a strong one and vice versa, so a
// caller that knows the underlying strength can derive the negation's strength.
SequencePropertyStrength NegatePropertyStrength(SequencePropertyStrength inner);

bool IsImmediateAssertionKindAllowed(AssertionKind kind);

enum class AssertionTiming : uint8_t {
  kImmediate = 0,
  kConcurrent = 1,
};

bool ConcurrentTimingUsesSampledValues(AssertionTiming timing);

enum class SampleMode : uint8_t {
  kPreponed = 0,
  kCurrent = 1,
  kDefault = 2,
};

struct SampledValue {
  uint64_t value = 0;
  SampleMode mode = SampleMode::kPreponed;
};

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default);

SampledValue SampleAutomaticVariable(uint64_t current_value);

SampledValue DefaultSampledValueOfTriggered();
SampledValue DefaultSampledValueOfMatched();

SampledValue SampleSingleVariableExpression(SampledValue var_sample);

SampledValue SampleConstCastExpression(uint64_t argument_current_value);

SampledValue SampleProceduralAssertionArgument(uint64_t current_value);

SampledValue ProceduralArgumentValueAfterMature(SampledValue captured,
                                                 uint64_t later_underlying_value);

enum class ProceduralExecutionEffect : uint8_t {
  kActivation = 0,
  kCompletion = 1,
};

bool ProceduralExecutionAffects(ProceduralExecutionEffect effect,
                                 bool already_matured);

SampledValue SampleProceduralAssertionActionBlockArgument(uint64_t current_value);

bool ActionBlockMayModifyArgument();

uint64_t ReadProceduralConditionalGuard(uint64_t current_value,
                                         uint64_t sampled_value);

SampledValue SampledValueOfTriggered(bool current_returned);
SampledValue SampledValueOfMatched(bool current_returned);

SampledValue SampleRecursiveExpression(
    SampledValue a, SampledValue b,
    uint64_t (*combinator)(uint64_t, uint64_t));

SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default);

// §16.6: a concurrent-assertion Boolean expression's result is interpreted
// the same way as the condition of a procedural `if`. With aval/bval dual
// rails, any unknown bit (bval != 0) makes the value false; otherwise the
// value is true iff aval is non-zero.
bool InterpretAssertionExprAsBoolean(uint64_t aval, uint64_t bval);

// §16.6: an element of a dynamic array, queue, or associative array that has
// been sampled for assertion expression evaluation must keep being readable
// until the evaluation completes, even if the array is later mutated. The
// `live` flag stays true across simulated mutation to model that lifetime.
struct SampledArrayElement {
  uint64_t value = 0;
  bool live = true;
};
SampledArrayElement SampleArrayElementForAssertion(uint64_t element_value);
SampledArrayElement ArrayElementAfterArrayMutation(SampledArrayElement sampled);
bool SampledArrayElementStillReadable(const SampledArrayElement& sampled);

// §16.6: where a Boolean expression can occur inside a concurrent assertion.
// The sampled-vs-current evaluation rule branches on this context: only
// sequence/property expressions use sampled values; clocking-event expressions
// are explicitly excepted (they follow §16.5), and disable-condition
// expressions are evaluated with current values.
enum class BooleanExprPlace : uint8_t {
  kSequenceOrPropertyExpr = 0,
  kClockingEvent = 1,
  kDisableCondition = 2,
};
bool BooleanExprUsesSampledValues(BooleanExprPlace place);

// §16.6: disable-condition specifics. The condition is evaluated against
// current values; `triggered` is callable from it, but `matched` and local
// variables are not.
bool DisableConditionUsesCurrentValues();
bool DisableConditionAllowsTriggeredMethod();
bool DisableConditionAllowsMatchedMethod();
bool DisableConditionAllowsLocalVariableReference();

enum class ClockingInputSkew : uint8_t {
  kStep1 = 0,
  kOther = 1,
};

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew);

struct DeferredAssertion {
  uint64_t condition_val = 0;
  std::string instance_name;
  std::function<void()> pass_action;
  std::function<void()> fail_action;
  AssertionSeverity severity = AssertionSeverity::kError;

  AssertionKind kind = AssertionKind::kAssert;

  bool has_else_clause = true;
};

void ExecuteDeferredAssertionAction(const DeferredAssertion& da);

bool UsesErrorSeverityFallback(const DeferredAssertion& da);

enum class DeferralKind : uint8_t {
  kObserved = 0,
  kFinal = 1,
};

enum class FlushPointReason : uint8_t {
  kNone = 0,
  kEventControlResume = 1,
  kWaitResume = 2,
  kAlwaysCombSignalDelta = 3,
  kAlwaysLatchSignalDelta = 4,
  kDisableOuterScope = 5,
};

bool IsDeferredFlushPoint(FlushPointReason reason);

struct PendingDeferredReport {
  std::string process_id;
  DeferralKind deferral = DeferralKind::kObserved;
  DeferredAssertion da;
  bool matured = false;
};

class DeferredReportQueue {
 public:
  void Enqueue(PendingDeferredReport report);
  void MatureObservedReports();
  void MatureFinalReports();
  std::vector<PendingDeferredReport> TakeMaturedObserved();
  std::vector<PendingDeferredReport> TakeMaturedFinal();
  void FlushNonMatured();

  // §16.4.4: disabling one specific deferred assertion cancels that
  // assertion's still-pending reports while leaving every other assertion's
  // pending reports, and any already-matured report of the named assertion, in
  // place.
  void FlushNonMaturedForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  uint32_t NonMaturedCount() const;
  const std::vector<PendingDeferredReport>& Entries() const { return entries_; }

 private:
  std::vector<PendingDeferredReport> entries_;
};

// §16.14.6.2: a process reaches a procedural assertion flush point when it
// resumes after suspending at an event control or wait, when an always_comb or
// always_latch process re-runs due to a dependent-signal transition, or when
// its outermost scope is disabled. Reaching such a point flushes the pending
// procedural concurrent assertion instances of that process. The flush-point
// conditions coincide with the deferred case, so the FlushPointReason values
// are shared; this predicate is the procedural-concurrent-assertion view of
// that classification.
bool IsProceduralAssertionFlushPoint(FlushPointReason reason);

struct PendingProceduralAssertion {
  AssertionKind kind = AssertionKind::kAssert;
  std::string instance_name;

  std::vector<SampledValue> sampled_args;
  bool matured = false;
};

class ProceduralAssertionQueue {
 public:
  void Enqueue(PendingProceduralAssertion pending);

  void MatureAll();

  void Flush();

  // §16.14.6.2: at a flush point only the instances that have not yet matured
  // are discarded; instances that already matured stay queued so they can
  // still proceed to evaluation.
  void FlushPending();

  // §16.14.6.4: disabling one specific procedural concurrent assertion clears
  // that assertion's still-pending instances from the queue while leaving every
  // other assertion's pending instances, and any already-matured instance of
  // the named assertion, in place.
  void FlushPendingForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  const std::vector<PendingProceduralAssertion>& Entries() const {
    return queue_;
  }

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// §16.14.6.4: a `disable` statement may name several kinds of object; which one
// it targets decides whether the addressed process's pending procedural
// concurrent assertion instances are flushed.
enum class DisableTarget : uint8_t {
  kSpecificAssertion = 0,
  kOutermostScope = 1,
  kNonOutermostScope = 2,
  kTask = 3,
};

// §16.14.6.4: disabling a specific procedural concurrent assertion, or the
// outermost scope of a procedure that has a pending procedural assertion queue,
// flushes pending procedural assertion instances; disabling a task or a
// non-outermost scope of a procedure does not.
bool DisableFlushesProceduralAssertions(DisableTarget target);

// §16.4.4: disabling a specific deferred assertion, or the outermost scope of a
// procedure that has an active deferred assertion report queue, clears pending
// reports; disabling a task or a non-outermost scope of a procedure does not.
bool DisableFlushesDeferredAssertions(DisableTarget target);

bool IsStaticConcurrentAssertion(bool appears_in_procedural_code);

bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic);

enum class InferredClockKind : uint8_t {
  kFromProceduralContext = 0,
  kFromDefaultClocking = 1,
  kNotInferrable = 2,
};

struct InferredClock {
  InferredClockKind kind = InferredClockKind::kNotInferrable;
  std::string_view signal_name;
};

InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock,
    std::string_view default_clock);

bool SatisfiesClockInferenceRequirements(bool no_blocking_timing_control,
                                          bool exactly_one_event_control,
                                          bool unique_qualifying_event_expr);

class MaturedAssertionQueue {
 public:
  void Place(PendingProceduralAssertion matured);

  std::vector<PendingProceduralAssertion> TakeAll();
  uint32_t Size() const;

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// §16.14.1: which branch of an assert statement's action_block runs after the
// property is evaluated. When the property holds, the pass statements run; when
// it fails, the fail statements run; when the property is disabled (e.g. by a
// `disable iff`), no action_block statement runs at all.
enum class AssertActionBlockChoice : uint8_t {
  kPass,
  kFail,
  kNone,
};

// §16.14.1: choose the action_block branch for an assert statement from the
// outcome of evaluating its property. A disabled evaluation suppresses the
// action_block entirely and takes precedence over the pass/fail distinction.
AssertActionBlockChoice SelectAssertActionBlock(bool property_passed,
                                                bool property_disabled);

// §16.14.1: the execution of the pass and fail statements can be controlled
// using the assertion action control tasks (see §20.11). This composes the base
// §16.14.1 choice with the per-instance pass/fail enables maintained for the
// §20.11 control tasks: a pass branch is suppressed when the pass action is
// disabled, and a fail branch is suppressed when the fail action is disabled.
AssertActionBlockChoice ResolveAssertActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled);

// §16.14.1: when the else clause is omitted, the tool calls $error on failure
// unless $assertcontrol has been used to suppress the failure (see §20.11).
// This is the §16.14.1 default-$error condition (UsesErrorSeverityFallback)
// gated by the §20.11 fail-action enable, so a FailOff control suppresses the
// otherwise-default $error.
bool CallsDefaultErrorOnFailure(const DeferredAssertion& da,
                                bool fail_action_enabled);

// §16.14.1: the conventions regarding default severity for a concurrent
// assertion action block are the same as for immediate assertions; the default
// severity is error.
AssertionSeverity DefaultConcurrentAssertActionSeverity();

// §16.14.1: the pass and fail statements of an assert statement are executed in
// the Reactive region.
Region ConcurrentAssertActionRegion();

// === §16.14.2 Assume statement ===

// §16.14.2: for simulation an assumed property is constrained to hold and, like
// an asserted property, is checked and reported when it fails. Its action_block
// branch follows the property outcome exactly as an assert statement's does: a
// true evaluation runs the pass statements, a false evaluation runs the fail
// statements, and a disabled evaluation runs neither. Delegating to the
// §16.14.1 selector keeps the assume and assert action-block behavior identical.
inline AssertActionBlockChoice SelectAssumeActionBlock(bool property_passed,
                                                       bool property_disabled) {
  return SelectAssertActionBlock(property_passed, property_disabled);
}

// §16.14.2: the pass and fail statements of an assume statement can be
// controlled with the §20.11 assertion action control tasks, the same way an
// assert statement's are.
inline AssertActionBlockChoice ResolveAssumeActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled) {
  return ResolveAssertActionUnderControl(base, pass_action_enabled,
                                         fail_action_enabled);
}

// §16.14.2: an assume statement has a fail action — unlike a cover statement —
// so when its else clause is omitted the tool calls $error on a failing
// evaluation, unless a §20.11 control has disabled the fail action. A disabled
// evaluation is neither a pass nor a fail, so the caller passes
// property_failed=false for it and no default $error is issued.
inline bool AssumeCallsDefaultErrorOnFailure(bool property_failed,
                                             bool has_else_clause,
                                             bool fail_action_enabled) {
  return property_failed && !has_else_clause && fail_action_enabled;
}

// §16.14.2: the directive that an assertion-biasing dist (an
// `expression dist { dist_list }`, defined in A.1.10) appears in determines how
// the dist operator is interpreted for random simulation.
enum class BiasedAssertionDirective : uint8_t {
  kAssert,
  kAssume,
  kCover,
};

// §16.14.2: when a property that uses biasing appears in an assert or cover
// statement, the dist operator is equivalent to the inside operator and the
// weight specification is ignored. Only in an assume statement do the weights
// take effect, biasing the random selection of free-variable values.
inline bool BiasingWeightsIgnored(BiasedAssertionDirective directive) {
  return directive == BiasedAssertionDirective::kAssert ||
         directive == BiasedAssertionDirective::kCover;
}

// §16.14.2: within an assert or cover statement a biased dist behaves as the
// inside operator — plain set membership with the weights dropped. In an assume
// statement the weights are honored, so the dist is not reduced to inside there.
inline bool BiasedDistActsAsInside(BiasedAssertionDirective directive) {
  return BiasingWeightsIgnored(directive);
}

// §16.14.2: a property that is assumed shall hold in the same way with or
// without biasing. The set of free-variable values that satisfy an assumption is
// the membership set of the distribution and does not depend on the weights;
// biasing only chooses among those legal values when there is a choice at a
// given time. Whether `value` is a legal selection is therefore independent of
// whether biasing weights are present.
inline bool AssumeValueIsLegalUnderBiasing(int64_t value,
                                           const std::vector<int64_t>& members,
                                           bool /*weights_present*/) {
  for (int64_t member : members) {
    if (member == value) return true;
  }
  return false;
}

// §16.14.2: for an assume statement the biasing weights select among the legal
// free-variable values according to their cumulative distribution. Given the
// per-candidate weights and a random draw in [0, sum(weights)), return the index
// of the chosen candidate. (In an assert or cover statement the weights are
// ignored, so this weighted selection does not apply there.)
inline std::size_t SelectBiasedFreeVariable(
    const std::vector<uint32_t>& weights, uint64_t draw) {
  uint64_t cumulative = 0;
  for (std::size_t i = 0; i < weights.size(); ++i) {
    cumulative += weights[i];
    if (draw < cumulative) return i;
  }
  return weights.empty() ? 0 : weights.size() - 1;
}

// === §16.14.4 Restrict statement ===

// §16.14.4: a restrict property statement shares the constraining semantics of
// assume property — it directs the tool to take the property as holding and
// bounds the explored state space the same way — so for formal analysis the two
// behave identically.
bool RestrictSharesAssumeConstraintSemantics();

// §16.14.4: in contrast to assume property, a restrict property statement is not
// verified in simulation. No pass/fail evaluation runs for it, so it never
// yields a run-time pass or fail result the way an assumed or asserted property
// does.
bool RestrictIsVerifiedInSimulation();

// §16.14.4: because a restrict is not verified in simulation, a cycle in which
// its property does not hold (e.g. a restricted ctr taking value 1) is not
// flagged — violating the restriction during simulation is not an error.
bool RestrictViolationIsSimulationError();

// === §16.14.5 Using concurrent assertion statements outside procedural code ===

// §16.14.5: a concurrent assertion statement used outside procedural code (a
// static concurrent assertion) follows `always` semantics — a new evaluation
// attempt of the underlying property_spec begins at every occurrence of its
// leading clock event. Over a run with the given number of leading clock ticks,
// that many attempts are started, so the property is checked from the beginning
// to the end of simulation.
int StaticConcurrentAssertionAttemptsStarted(int leading_clock_ticks);

// §16.14.5: an `assert property (ps) action_block` written outside procedural
// code is equivalent to `always assert property (ps) action_block;`.
bool StaticAssertEquivalentToAlwaysAssert();

// §16.14.5: a `cover property (ps) statement_or_null` written outside procedural
// code is equivalent to `always cover property (ps) statement_or_null`.
bool StaticCoverEquivalentToAlwaysCover();

// §16.9.4: the global clocking past value-change functions compare the sampled
// value at the global clock tick that immediately precedes the current tick
// with the value at the current tick. $rose_gclk reports the LSB changing to 1,
// $fell_gclk the LSB changing to 0, $stable_gclk the whole expression being
// unchanged, and $changed_gclk the whole expression having changed.
bool RoseGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool FellGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool StableGclk(uint64_t prev_value, uint64_t cur_value);
bool ChangedGclk(uint64_t prev_value, uint64_t cur_value);

// §16.9.4: the global clocking future value-change functions are the same
// except that they use the subsequent value of the expression, sampled at the
// next global clock tick. $rising_gclk reports the LSB changing to 1 and
// $falling_gclk the LSB changing to 0 at the next global clock tick;
// $steady_gclk reports the expression not changing at the next tick; and
// $changing_gclk is the complement of $steady_gclk.
bool RisingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool FallingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool SteadyGclk(uint64_t cur_value, uint64_t next_value);
bool ChangingGclk(uint64_t cur_value, uint64_t next_value);

// §16.9.4: execution of the action block of an assertion containing global
// clocking future sampled value functions is delayed until the global clock
// tick that follows the last tick of the assertion clock for the attempt. When
// the attempt fails and $error is called by default (see §16.14.1), that $error
// is likewise issued at that following global clock tick rather than at the
// last assertion-clock tick.
bool GclkFutureActionBlockDelayedToFollowingGlobalTick();

// §16.9.4: the behavior of asynchronous controls such as $assertcontrol (see
// §20.11) is with respect to the interval of the evaluation attempt, whose end
// is the last tick of the assertion clock. A $assertcontrol Kill (control_type
// 5) executed in a time step strictly after that last tick does not affect the
// attempt, even if it runs no later than the following global clock tick. The
// parameter is true when the Kill occurs at or before the last assertion-clock
// tick.
bool GclkFutureKillAffectsAttempt(bool kill_at_or_before_last_assertion_tick);

// §20.11: the integer control_type argument selects the effect of the
// $assertcontrol system task. The values are those of Table 20-5.
enum class AssertControlType : uint8_t {
  kLock = 1,
  kUnlock = 2,
  kOn = 3,
  kOff = 4,
  kKill = 5,
  kPassOn = 6,
  kPassOff = 7,
  kFailOn = 8,
  kFailOff = 9,
  kNonvacuousOn = 10,
  kVacuousOff = 11,
};

// §20.11: when assertion_type is not specified it defaults to 255, so the task
// applies to all assertion types, expect statements, and violation reports. The
// bit values are those of Table 20-6.
inline constexpr uint32_t kAssertionTypeDefault = 255;

// §20.11: when directive_type is not specified it defaults to 7
// (Assert|Cover|Assume), so the task applies to all directive types. The bit
// values are those of Table 20-7.
inline constexpr uint32_t kDirectiveTypeDefault = 7;

// §20.11: Table 20-6 assertion_type bit values. A $assertcontrol assertion_type
// argument is an OR of these, selecting which assertion and report kinds the
// task affects.
enum class AssertionTypeBit : uint32_t {
  kConcurrent = 1,
  kSimpleImmediate = 2,
  kObservedDeferredImmediate = 4,
  kFinalDeferredImmediate = 8,
  kExpect = 16,
  kUnique = 32,
  kUnique0 = 64,
  kPriority = 128,
};

// §20.11: Table 20-7 directive_type bit values. A $assertcontrol directive_type
// argument is an OR of these, selecting which directive kinds the task affects.
enum class DirectiveTypeBit : uint32_t {
  kAssert = 1,
  kCover = 2,
  kAssume = 4,
};

// §20.11: the assertion_type argument selects assertion/report kinds by OR-ing
// Table 20-6 values; a task affects an assertion when that assertion's type bit
// is set in the mask. For example, mask 3 (Concurrent|SimpleImmediate) affects
// concurrent and simple immediate assertions but not deferred ones.
bool ControlAffectsAssertionType(uint32_t assertion_type_mask,
                                 AssertionTypeBit bit);

// §20.11: the directive_type argument selects directive kinds by OR-ing Table
// 20-7 values; a task affects a directive when that directive's bit is set in
// the mask. For example, mask 3 (Assert|Cover) affects assert and cover
// directives but not assume directives.
bool ControlAffectsDirectiveType(uint32_t directive_type_mask,
                                 DirectiveTypeBit bit);

// §20.11: the assertion action control tasks, and $assertcontrol with a
// control_type from 6 (PassOn) through 11 (VacuousOff), do not affect the
// statistics counters for the assertions; the status controls 1 (Lock) through
// 5 (Kill) do.
bool ControlTypeAffectsStatistics(int control_type);

// §20.11: the convenience and backward-compatibility tasks are defined in terms
// of $assertcontrol. This records the equivalent control_type, assertion_type,
// and directive_type a named task expands to.
struct AssertControlInvocation {
  uint32_t control_type = 0;
  uint32_t assertion_type = 0;
  uint32_t directive_type = 0;
};

// §20.11: expand a convenience assertion control task name (with the leading
// '$') to its equivalent $assertcontrol invocation. The $asserton/$assertoff/
// $assertkill tasks expand with assertion_type 15 and the action control tasks
// with assertion_type 31; both use directive_type 7. Returns false for a name
// that is not one of the convenience tasks.
bool EquivalentAssertControlForTask(std::string_view task_name,
                                    AssertControlInvocation& out);

class AssertionControl {
 public:
  bool IsEnabled(std::string_view inst) const;
  void SetOff(std::string_view inst);
  void SetOn(std::string_view inst);
  void Kill(std::string_view inst);
  bool WasKilled(std::string_view inst) const;

  void SetGlobalOff();
  void SetGlobalOn();

  // §20.11: Lock (control_type 1) prevents any status change of the named
  // assertion until it is unlocked; while locked, no $assertcontrol affects it.
  // Unlock (control_type 2) removes the locked status.
  void Lock(std::string_view inst);
  void Unlock(std::string_view inst);
  bool IsLocked(std::string_view inst) const;

  bool IsPassEnabled(std::string_view inst) const;
  void SetPassOff(std::string_view inst);
  // §20.11: PassOn (control_type 6) re-enables the pass action for both vacuous
  // and nonvacuous success.
  void SetPassOn(std::string_view inst);

  // §20.11: NonvacuousOn (control_type 10) enables the pass action on
  // nonvacuous success; VacuousOff (control_type 11) stops the pass action on
  // vacuous success. Pass enablement is therefore tracked per success kind.
  bool IsVacuousPassEnabled(std::string_view inst) const;
  bool IsNonvacuousPassEnabled(std::string_view inst) const;
  void SetNonvacuousOn(std::string_view inst);
  void SetVacuousOff(std::string_view inst);

  bool IsFailEnabled(std::string_view inst) const;
  void SetFailOff(std::string_view inst);
  void SetFailOn(std::string_view inst);

  // §20.11: apply a $assertcontrol invocation by its integer control_type to
  // the named assertion. A locked assertion is unaffected by any control_type
  // other than Unlock.
  void ApplyControl(int control_type, std::string_view inst);

 private:
  bool global_off_ = false;
  std::unordered_set<std::string> disabled_;
  std::unordered_set<std::string> killed_;
  std::unordered_set<std::string> locked_;
  std::unordered_set<std::string> vacuous_pass_off_;
  std::unordered_set<std::string> nonvacuous_pass_off_;
  std::unordered_set<std::string> fail_off_;
};

// §16.17: the expect statement is a blocking statement that waits on a property
// evaluation. When activated it starts a single evaluation thread, and the
// outcome of that thread drives both whether the process keeps blocking and
// which arm of the action block runs. These pure helpers encode that behavior
// independent of the surrounding scheduling machinery.
enum class ExpectActionKind : uint8_t {
  kBlock,        // property still pending — the process stays blocked
  kRunPass,      // property succeeded — take the action block's pass arm
  kRunFail,      // property failed and an else clause is present
  kReportError,  // property failed with no else clause — call $error
};

// §16.17: map an expect property's evaluation outcome onto the action the
// expecting process takes. While the property is pending the process remains
// blocked. On success the optional pass statement runs. On failure the else
// clause runs when present; otherwise the tool reports the failure via $error
// (the $assertcontrol suppression of §20.11 is applied by that machinery).
ExpectActionKind ResolveExpectAction(PropertyResult result,
                                     bool has_else_clause);

// §16.17: the expecting process blocks until the property succeeds or fails,
// and is unblocked exactly when the evaluation resolves. While the result is
// pending it stays blocked and the single evaluation thread keeps running; once
// the property resolves it stops being evaluated.
bool ExpectProcessRemainsBlocked(PropertyResult result);

// §16.17: when executed, an expect statement starts its evaluation on the
// subsequent clocking event — the first evaluation takes place on the next
// clocking event, never on one coincident with the tick at which the expect
// was activated. Returns true for a clocking event strictly after that tick.
bool ExpectClockingEventBeginsEvaluation(uint64_t activation_tick,
                                         uint64_t clocking_event_tick);

// §16.17: the statement following the expect, and the action block, run after
// the Observed region in which the property completes its evaluation — i.e. in
// the Reactive region of that time step.
inline constexpr Region ExpectResumeRegion() { return Region::kReactive; }

// §16.17: when the else clause is omitted, the tool reports a failed expect by
// calling $error, i.e. at error severity.
inline constexpr AssertionSeverity ExpectDefaultFailSeverity() {
  return AssertionSeverity::kError;
}

class SvaEngine {
 public:
  void QueueDeferredAssertion(const DeferredAssertion& da);
  void QueueDeferredAssertionIfEnabled(const DeferredAssertion& da);
  void FlushDeferredAssertions(Scheduler& sched, SimTime time);
  void FlushDeferredAssertionsRespectingControl(Scheduler& sched, SimTime time);
  void KillAssertionsForInstance(std::string_view inst);

  uint32_t DeferredQueueSize() const;
  AssertionControl& GetControl() { return control_; }

  ProceduralAssertionQueue& GetProceduralQueue(std::string_view process_id);

  void QueuePendingReport(std::string_view process_id,
                          const DeferredAssertion& da,
                          DeferralKind kind);

  void MatureObservedReports(std::string_view process_id);
  void MatureFinalReports(std::string_view process_id);

  uint32_t ExecuteMaturedObservedInReactive(std::string_view process_id,
                                            Scheduler& sched, SimTime time);
  uint32_t ExecuteMaturedFinalInPostponed(std::string_view process_id,
                                          Scheduler& sched, SimTime time);

  void OnDeferredFlushPoint(std::string_view process_id,
                            FlushPointReason reason);

  void OnProceduralAssertionFlushPoint(std::string_view process_id,
                                       FlushPointReason reason);

  // §16.14.6.4: apply a `disable` statement's effect on a process's pending
  // procedural concurrent assertion queue. Disabling the named specific
  // assertion clears only that assertion's pending instances; disabling the
  // outermost scope flushes the whole pending queue; disabling a task or a
  // non-outermost scope leaves the queue untouched. Already-matured attempts
  // are never affected. The normal disable activities of §9.6.2 happen
  // elsewhere, in addition to this queue effect.
  void ApplyDisableToProceduralAssertions(std::string_view process_id,
                                          DisableTarget target,
                                          std::string_view assertion_instance);

  // §16.4.4: apply a `disable` statement's effect on a process's deferred
  // assertion report queue. Disabling the named specific deferred assertion
  // cancels only that assertion's pending reports; disabling the outermost
  // scope clears all pending reports on the queue; disabling a task or a
  // non-outermost scope leaves the queue untouched. Already-matured reports are
  // never affected. The normal disable activities of §9.6.2 happen elsewhere,
  // in addition to this queue effect.
  void ApplyDisableToDeferredAssertions(std::string_view process_id,
                                        DisableTarget target,
                                        std::string_view assertion_instance);

  DeferredReportQueue& GetDeferredReportQueue(std::string_view process_id);
  const DeferredReportQueue* PeekDeferredReportQueue(
      std::string_view process_id) const;

 private:
  std::vector<DeferredAssertion> deferred_queue_;
  AssertionControl control_;
  std::unordered_map<std::string, ProceduralAssertionQueue> procedural_queues_;
  std::unordered_map<std::string, DeferredReportQueue> per_process_reports_;
};

}
