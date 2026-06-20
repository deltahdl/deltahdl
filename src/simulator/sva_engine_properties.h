#ifndef DELTA_SIMULATOR_SVA_ENGINE_PROPERTIES_H_
#define DELTA_SIMULATOR_SVA_ENGINE_PROPERTIES_H_

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/sva_engine_sequences.h"

namespace delta {


// §16.12.7: an implication `sequence_expr |-> property_expr` (overlapped) or
// `sequence_expr |=> property_expr` (nonoverlapped) preconditions the
// consequent property_expr on a match of the antecedent sequence_expr. When the
// antecedent has no match the implication holds vacuously. The overlapped form
// evaluates the consequent at the end point of the match, so the result is the
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
// form (no else) holds vacuously when the guard is false, since there is
// nothing to check; the two-branch form routes a false guard to the else-branch
// instead.
PropertyResult EvalPropertyIfElse(bool cond, PropertyResult then_result,
                                  bool has_else, PropertyResult else_result);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);

// §16.12.16: one ordinary item of a case property statement as the linear
// search sees it — whether this item's expression_or_dist matched the case
// expression (the comparison itself follows the §12.5 rules) and the verdict of
// the item's property_expr. The default item is never represented here: it is
// excluded from the scanned list so it cannot be picked up by the search.
struct PropertyCaseBranch {
  bool selected = false;
  PropertyResult result = PropertyResult::kVacuousPass;
};

// §16.12.16: evaluate a case property statement. The ordinary items are scanned
// in source order; the first one whose expression matches the case expression
// is the single property_expr that contributes the verdict, and the search
// stops there, so later items are never reached. The default item is held apart
// from the scan and consulted only when no ordinary item matches: when a
// default is present its property_expr supplies the verdict, and when none is
// present the case property succeeds vacuously (a true verdict).
PropertyResult EvalPropertyCase(const std::vector<PropertyCaseBranch>& branches,
                                bool has_default,
                                PropertyResult default_result);

// §16.12.7: settles a deferred nonoverlapped (|=>) implication once the clock
// reaches the tick after the antecedent match, where the consequent is finally
// evaluated.
PropertyResult ResolveNonOverlapping(bool consequent_matched);

// §16.12.8: a property `property_expr1 implies property_expr2` evaluates to
// true if, and only if, the antecedent fails to hold or the consequent holds —
// the ordinary logical implication over the two operands' verdicts. Unlike the
// sequence implication operators of §16.12.7 there is no antecedent match point
// to defer to, so the result settles from the operand verdicts directly. A
// vacuous pass counts as the operand holding, mirroring EvalPropertyOr.
PropertyResult EvalPropertyImplies(PropertyResult antecedent,
                                   PropertyResult consequent);

// §16.12.8: a property `property_expr1 iff property_expr2` evaluates to true
// if, and only if, both operands hold or both operands fail to hold — the
// operands' verdicts must agree. A vacuous pass counts as the operand holding.
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

// §16.12.9: settles a deferred nonoverlapped followed-by (#=#) at the tick
// after the antecedent match, where the consequent property_expr is finally
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
// the obligation could be disproven), strongly it fails (the required tick
// never arrived). When the target tick is reachable the nexttime verdict is
// exactly the property_expr's verdict at that tick.
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

// §16.12.11: outcome of an `always`/`s_always` property over its window of
// clock ticks. `strong` selects `s_always` (strong) versus `always` (weak).
// `all_covered_ticks_present` says whether every clock tick the range demands
// is actually present; only the strong form requires the covered ticks to
// exist, since for a weak always it is not required that all clock ticks within
// the range exist. `inner_holds_at_present_ticks` says whether the inner
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

// §16.12.11: for a strong always, every clock tick the range covers shall
// exist. Counting starts at the current time step, so the covered ticks all
// exist when at least `range_max` further ticks are available after the current
// step.
bool AlwaysStrongTicksAllPresent(int range_max, int future_clock_ticks);

// §16.12.12: sentinel for the offset of the first tick at which the right
// operand of an until property holds, used when it never holds at any current
// or future clock tick.
inline constexpr int kUntilRhsNever = -1;

// §16.12.12: whether the left operand holds at every clock tick it is required
// to for an until property. `lhs_run_length` is the number of consecutive
// ticks, starting at the evaluation attempt, at which the left operand holds.
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
// present clock tick within the range. `all_range_ticks_present` is whether
// every clock tick the range covers exists. The strong form requires such a
// witness and fails when none is found; the weak form also holds when the
// range's ticks do not all exist, since it does not require those later ticks
// to be present.
PropertyResult EvalEventually(bool strong, bool inner_holds_within_range,
                              bool all_range_ticks_present);

// §16.12.14: an accept abort property (accept_on / sync_accept_on) evaluates
// the underlying property_expr, but if the abort condition becomes true during
// that evaluation the overall result is forced to true; otherwise the result is
// the underlying verdict. The abort condition takes precedence, so a true
// condition wins even over an underlying verdict that has already settled.
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
// evaluation is true if, and only if, there is a match of the sequence
// beginning at that point. Like a singly clocked property the result is always
// a definite true or false, never pending.
PropertyResult EvalMulticlockedSequenceAsProperty(bool sequence_has_match);

// §16.13.2: a Boolean `and` whose two operands are clocked by different clocks
// forms a multiclocked property — but not a multiclocked sequence. Both
// operands begin at the same evaluation point, each on its own clock; the
// conjunction is true if, and only if, both operands have a match beginning at
// that point.
PropertyResult EvalMulticlockedAnd(bool left_operand_has_match,
                                   bool right_operand_has_match);

// §16.13.2: sentinel returned when no tick of the relevant clock is available
// to locate the evaluation point of a multiclocked operand.
inline constexpr uint64_t kNoMulticlockTick = ~static_cast<uint64_t>(0);

// §16.13.2: the nearest tick of `clock_ticks` at which a multiclocked operand
// is evaluated relative to time `from`. When `inclusive` is true a tick
// coincident with `from` qualifies (the "possibly overlapping" / "non-strictly
// subsequent" reading); when false only strictly future ticks qualify.
// `clock_ticks` shall be in increasing time order. Returns kNoMulticlockTick
// when no qualifying tick exists.
uint64_t NearestClockTickAtOrAfter(uint64_t from,
                                   const std::vector<uint64_t>& clock_ticks,
                                   bool inclusive);

// §16.13.2: the tick at which the consequent of a multiclocked implication is
// evaluated. Both forms synchronize from the antecedent match end time to a
// tick of the consequent's clock. The nonoverlapping form (|=>) advances to the
// nearest strictly future consequent-clock tick. The overlapping form (|->)
// awaits the nearest consequent-clock tick: when the consequent clock ticks at
// the antecedent end the consequent is checked there immediately, otherwise it
// behaves as the nonoverlapping form. Returns kNoMulticlockTick when no
// qualifying consequent-clock tick exists.
uint64_t MulticlockedConsequentEvalTick(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

// §16.13.2: whether a multiclocked overlapping implication (|->) checks its
// consequent immediately, i.e. the consequent clock ticks at the antecedent
// match end. The nonoverlapping form (|=>) never checks immediately because it
// advances to a strictly future tick.
bool MulticlockedImplicationChecksImmediately(
    uint64_t antecedent_end_time,
    const std::vector<uint64_t>& consequent_clock_ticks, bool overlapping);

// §16.13.2: the tick at which a branch of a multiclocked if / if-else property
// is evaluated. The condition is checked at the property clock
// (`condition_time`); the then-branch is then evaluated at the nearest,
// possibly overlapping tick of its clock and the else-branch at the nearest
// non-strictly subsequent tick of its clock. Both readings admit a tick
// coincident with the condition check, so the branch tick is the nearest tick
// at or after `condition_time`. Returns kNoMulticlockTick when the branch clock
// has no qualifying tick.
uint64_t MulticlockedIfBranchEvalTick(
    uint64_t condition_time, const std::vector<uint64_t>& branch_clock_ticks);

// §16.13.7: one copy of a named sequence/property local variable, created for a
// single semantic leading clock of the instance, together with the time step at
// which this copy's initialization assignment is performed.
struct LocalVarInitCopy {
  // Index of the semantic leading clock (into the per-leading-clock tick lists)
  // that governs this copy and the subproperty the copy is used in.
  size_t leading_clock_index;
  // Earliest tick of that leading clock at or after the start of the evaluation
  // attempt — the time step where this copy's init assignment is performed.
  // kNoMulticlockTick when that leading clock has no qualifying tick.
  uint64_t init_tick;
};

// §16.13.7: for a singly clocked sequence or property, the local variable
// initialization assignment of an evaluation attempt is performed when the
// attempt begins, and such an attempt always begins at a tick of the single
// governing clock. The init thus happens at the attempt-begin time itself.
uint64_t SinglyClockedLocalInitTick(uint64_t attempt_begin);

// §16.13.7: for a multiclock instance with a single semantic leading clock (see
// §16.16.1), the local variable initialization assignment shall be performed at
// the earliest tick of that leading clock at or after the beginning of the
// evaluation attempt. A tick coincident with the begin qualifies. Returns
// kNoMulticlockTick when the leading clock has no qualifying tick.
uint64_t MulticlockedLocalInitTick(
    uint64_t attempt_begin, const std::vector<uint64_t>& leading_clock_ticks);

// §16.13.7: the number of copies of a local variable an evaluation attempt
// holds. A separate copy shall be created for each distinct semantic leading
// clock of the named property instance, so two or more distinct leading clocks
// yield two or more independent copies.
size_t LocalVarCopyCount(size_t distinct_semantic_leading_clocks);

// §16.13.7: the per-copy initialization schedule for a multiclock named
// property instance. One copy is created for each distinct semantic leading
// clock (passed as its own tick list, in increasing time order). For each copy
// the init assignment shall be performed at the earliest tick of its leading
// clock at or after the attempt begin, and that copy shall be used in
// evaluating the subproperty governed by the same leading clock.
std::vector<LocalVarInitCopy> MulticlockedLocalInitCopies(
    uint64_t attempt_begin,
    const std::vector<std::vector<uint64_t>>& per_leading_clock_ticks);

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
// (until, s_until) the witness is either operand's attempt being nonvacuous;
// for the overlapping forms (until_with, s_until_with) only the left operand's
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

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_PROPERTIES_H_
