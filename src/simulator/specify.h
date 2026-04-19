#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

// =============================================================================
// Runtime path delay entry (§30.3)
// =============================================================================

struct PathDelay {
  std::string src_port;
  std::string dst_port;
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;
  uint8_t delay_count = 1;   // 1, 2, 3, 6, or 12
  uint64_t delays[12] = {};  // A.7.4 transition delays:
  // [0]=rise/t01, [1]=fall/t10, [2]=z/t0z,
  // [3]=tz1, [4]=t1z, [5]=tz0,
  // [6]=t0x, [7]=tx1, [8]=t1x, [9]=tx0, [10]=txz, [11]=tzx

  // §30.7: per-transition pulse filtering limits. Indexed identically to
  // `delays`. The runtime invariant is error_limit[i] >= reject_limit[i]
  // for every slot. Both default to the matching `delays[i]` until a
  // descendant mechanism (PATHPULSE$, invocation options, or SDF) revises
  // them.
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

// §30.5.1: a path delay expression that evaluates to a negative value shall
// be treated as zero. Callers that have reduced a delay expression to a
// signed integer funnel through this helper before writing to PathDelay.
uint64_t ClampPathDelay(int64_t signed_value);

// §30.5.1 / Table 30-2: expand an N-delay input (N in {1,2,3}) across the
// six non-x transition slots of `pd.delays`. For N in {6,12} the expansion
// is an identity. Slots [6..11] (x-transition slots) are outside §30.5.1 and
// are never written by this helper.
void ExpandTransitionDelays(PathDelay& pd);

// §30.5.3: a candidate specify path considered during delay selection. The
// caller supplies one entry per path that could drive the output now being
// scheduled, annotating each with the input's most-recent transition time
// and the runtime-evaluated truth of the path's condition. Unconditioned
// paths always set `condition_true` to true.
struct PathCandidate {
  const PathDelay* path = nullptr;
  uint64_t last_transition_time = 0;
  bool condition_true = true;
};

// §30.5.3: returns the smallest `delays[transition_slot]` among the active
// candidates. A candidate is active when its input transitioned at the
// latest timestamp seen in `candidates` and its condition is true. Returns
// zero when no active candidate exists (including when the list is empty
// or every survivor's condition is false).
uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot);

// §30.6: for an input-to-output path that has both a specify-block module
// path delay and one or more distributed (gate instance) delays along it,
// the runtime must use the larger of the two. Callers supply the module
// path delay and the pre-summed distributed delay for the same path.
uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum);

// §30.7: outcome of filtering a pulse observed on a module path output.
// kPropagate emits the pulse unchanged; kForceX drives the destination to
// logic x for the duration the pulse would have lasted; kReject suppresses
// the pulse entirely.
enum class PulseClassification : uint8_t {
  kPropagate,
  kForceX,
  kReject,
};

// §30.7: classify a pulse of width `pulse_width` against the limits taken
// from the trailing-edge transition slot. Callers must enforce the
// invariant error_limit >= reject_limit; when they coincide the X band is
// empty and the classifier returns either kPropagate or kReject only.
PulseClassification ClassifyPulse(uint64_t pulse_width,
                                  uint64_t reject_limit,
                                  uint64_t error_limit);

// §30.7: copy every `delays[i]` into the matching `reject_limit[i]` and
// `error_limit[i]` slot, establishing the default inertial-delay behavior
// in which any pulse narrower than the path delay is rejected.
void InitDefaultPulseLimits(PathDelay& pd);

// §30.7.1: apply a pulse_control_specparam override. `reject` is written to
// every `reject_limit[i]`; `error_limit[i]` is set to `error` when the source
// supplied both limits (`has_error == true`) and mirrors `reject` otherwise,
// reflecting the LRM rule that a single-value PATHPULSE$ collapses the X band
// to zero. The propagation delays in `pd.delays` are not touched.
void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error);

// §30.7.2: apply the two global pulse-limit invocation percentages to `pd`.
// `reject_pct` and `error_pct` are integers in [0, 100]. Each transition
// slot's reject/error limit is derived by scaling the matching `delays[i]`
// by the corresponding percentage. When `error_pct < reject_pct` the error
// percentage is silently raised to the reject percentage so the resulting
// X band is never invalid. Callers are expected to order this helper after
// `InitDefaultPulseLimits` and before `ApplyPulseControlOverride`, so that
// PATHPULSE$ values take precedence when both are present.
void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct);

// §30.7.3: apply SDF-annotated pulse limits. `reject` is written to every
// `reject_limit[i]`; `error_limit[i]` receives `error` when the SDF entry
// supplied both values (`has_error == true`) and mirrors `reject` otherwise.
// Callers must invoke this helper after both `ApplyGlobalPulseLimits` and
// `ApplyPulseControlOverride` so that SDF values take precedence whenever
// all three mechanisms apply to the same path. The propagation delays in
// `pd.delays` are not touched.
void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error);

// =============================================================================
// Runtime timing check entry (§31)
// =============================================================================

struct TimingCheckEntry {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  uint64_t limit = 0;
  uint64_t limit2 = 0;  // Second limit for $setuphold/$recrem
  // §31.9: sign-preserving variants of `limit` / `limit2` for $setuphold
  // and $recrem only. When `negative_timing_check_enabled` is true, the
  // runtime reads the effective setup/hold (or recovery/removal) limits
  // from `signed_limit` and `signed_limit2` and ignores the two unsigned
  // fields above. Allowing the limits to be negative lets the violation
  // window sit entirely before or after the reference edge instead of
  // straddling it, matching the LRM's picture of disparate internal
  // clock and data delays. The flag defaults to off so every existing
  // non-negative entry continues through the baseline §31.3 path.
  bool negative_timing_check_enabled = false;
  int64_t signed_limit = 0;
  int64_t signed_limit2 = 0;
  // §31.4.4: $width glitch-suppression threshold. Defaults to zero per the
  // LRM, so unset entries behave as if no threshold was supplied and every
  // pulse narrower than `limit` witnesses a violation.
  uint64_t threshold = 0;
  // §31.4.6: $nochange start_edge_offset and end_edge_offset. Signed
  // because the LRM explicitly allows negative offsets to shrink the
  // violation region; zero-initialised, leaving the region equal to the
  // reference signal's level interval when unset.
  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  std::string notifier;
};

// §31.4.2: classify whether a single $timeskew observation interval
// reports a violation. `ref_time` is the timestamp event time;
// `next_event_time` is the time of the next observed event, with
// `next_event_is_data` distinguishing a data event (timecheck event,
// true) from a fresh reference event (false). `limit` is the configured
// non-negative skew limit. With `event_based_flag` false (the default),
// $timeskew is timer-based: a violation is reported when any event —
// data or a fresh reference — arrives strictly past the elapsed limit,
// and the boundary case where the next event lands exactly at
// `ref_time + limit` does not violate. With `event_based_flag` set,
// $timeskew behaves like $skew: only a data event strictly past the
// limit can violate, and a fresh reference event silently re-arms the
// wait. This helper captures the per-interval classification only;
// multi-interval dormancy (the quiet period until the next reference
// event after a violation) is the caller's responsibility.
bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag);

// §31.4.3: classify whether a single $fullskew observation interval
// reports a violation. `timestamp_time` is the time of the timestamp
// event (whichever of the reference_event or data_event transitioned
// first for this interval); `next_event_time` is the time of the next
// observed event, with `next_event_is_timecheck` distinguishing the
// timecheck event of the same interval (true) from a fresh timestamp
// event (false). `limit` is the configured non-negative skew limit —
// callers pass limit 1 when the reference transitioned first and
// limit 2 when the data event transitioned first, matching the two
// directional windows §31.4.3 defines. With `event_based_flag` false
// (the default), $fullskew is timer-based: a violation is reported
// when any event — timecheck or a fresh timestamp — arrives strictly
// past the elapsed limit, and the exact-expiration boundary is
// excluded. With `event_based_flag` set, $fullskew behaves like $skew
// for that window: only a timecheck event strictly past the limit can
// violate, and a fresh timestamp event silently re-arms the wait.
// This helper captures the per-interval classification only;
// multi-interval dormancy is the caller's responsibility.
bool ReportsFullskewViolation(uint64_t timestamp_time,
                              uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag);

// §31.6 Table 31-13: compute the post-violation value of a scalar notifier
// variable given its pre-violation value, expressed as a single-bit
// Logic4Word (only the low bit of aval/bval is consulted). The three
// non-z pre-states toggle deterministically: 0 becomes 1, 1 becomes 0,
// and x becomes 0 — the latter resolving the LRM's "Either 0 or 1"
// allowance in the direction that lets the following violation re-enter
// the 0↔1 cycle. A z pre-state is returned unchanged so an
// unconnected notifier cannot be driven by violations.
Logic4Word ToggleNotifierOnViolation(Logic4Word current);

// §31.7: the syntactic form of a `&&&` scalar_timing_check_condition,
// enumerated so the downstream enablement decision can dispatch on the
// top-level operator of the condition expression. The six members cover
// the full scalar_timing_check_condition grammar production: a bare
// expression, its bitwise negation, and the two case-{equality,
// inequality} and two plain-{equality, inequality} comparison forms
// against a scalar_constant.
enum class TimingCheckConditionKind : uint8_t {
  kPlain,    // expression
  kNegate,   // ~ expression
  kEq,       // expression ==  scalar_constant
  kCaseEq,   // expression === scalar_constant
  kNeq,      // expression !=  scalar_constant
  kCaseNeq,  // expression !== scalar_constant
};

// §31.7: classify a condition by the LRM's deterministic-vs-nondeterministic
// split. The plain, negated, case-equality, and case-inequality forms are
// deterministic — an x on the conditioning signal must not enable the
// timing check. The equality and inequality forms are nondeterministic —
// an x on the conditioning signal must still enable the timing check.
// The two classes drive different handling inside TimingCheckConditionEnables.
bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind);

// §31.7: decide whether a `&&&`-conditioned timing check is enabled, given
// the kind of the scalar_timing_check_condition, the LSB of the
// conditioning signal's value (already reduced to a single bit per the
// LRM's multibit-to-LSB rule), and — for the four comparison forms — the
// scalar_constant operand as a 0/1 bit. When the LSB is a known 0 or 1
// the decision matches the operator's four-valued arithmetic. When the
// LSB is x, the deterministic operators return false and the
// nondeterministic operators return true, overriding whatever the
// operator's natural evaluation would yield; the scalar_constant_bit
// argument is ignored for the non-comparison forms.
bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit);

// §31.8: whether a timing check takes its reference and data events from
// the same signal. The LRM calls these "timing checks with only a single
// signal" and names $period and $width as the exemplars. The classifier
// drives the vector-expansion count below: a single-signal check of width
// N expands to N per-bit checks, while a two-signal check of widths M
// and N expands to M*N. Kinds not listed here are two-signal.
bool IsSingleSignalTimingCheck(TimingCheckKind kind);

// §31.8: the two ways an implementation treats a vector terminal in a
// timing check. `kSingle` is the default: a vector participates as a
// unified signal, and a transition on any bit is considered a single
// transition of that vector, yielding one timing check per invocation.
// `kPerBit` is the optional mode the LRM allows a simulator to expose,
// in which a vector is expanded bit-by-bit so that each bit becomes
// its own timing check.
enum class TimingCheckVectorMode : uint8_t {
  kSingle,
  kPerBit,
};

// §31.8: number of unique timing-check instances produced for a single
// invocation given the reference and data terminal widths. In `kSingle`
// mode the answer is always one, regardless of the widths. In `kPerBit`
// mode the answer is `ref_width` for a single-signal check (the data
// event is derived from the reference signal, so the data width does
// not contribute) and `ref_width * data_width` for a two-signal check.
// A zero width on either input collapses the product to zero so callers
// that cannot determine a width upstream observe "no expansion" rather
// than a spurious count.
uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode);

// §31.9.1: whether a given timing-check kind consumes the delayed
// versions of its data and reference signals when the negative-timing
// option is enabled. The nine window-based and single-signal kinds
// ($setup, $hold, $setuphold, $recovery, $removal, $recrem, $width,
// $period, $nochange) consume the delayed signals so that their
// notifiers toggle at the proper moment. The three event-order kinds
// ($skew, $fullskew, $timeskew) must not, because delaying their
// inputs can reverse the observed order of transitions and cause the
// notifiers to fire at the wrong time relative to the rest of the
// model.
bool TimingCheckUsesDelayedSignals(TimingCheckKind kind);

// §31.9.1: outcome of adjusting a setup, hold, recovery, or removal
// limit for the internal shift that makes the violation window overlap
// the delayed reference signal. `limit` is the non-negative value to
// install on the TimingCheckEntry — either the unchanged adjusted
// value when it stays strictly positive, or zero when the LRM's
// less-than-or-equal-to-zero rule clamps it. `warn` records whether
// the simulator must emit the warning the LRM requires on every
// clamp.
struct AdjustedNegativeTimingLimit {
  uint64_t limit;
  bool warn;
};

// §31.9.1: clamp an adjusted negative-timing-check limit to zero when
// the adjustment pushed it to or below zero, and signal the warning
// the LRM requires in that case. A strictly positive input is
// returned unchanged with `warn` false; any value at or below zero
// collapses to zero with `warn` set. The helper does not differentiate
// between the negative-adjustment and exactly-zero paths because the
// LRM folds both into the same rule.
AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit);

// §31.9.1 rule (a): whether a negative-timing-check violation window
// is wide enough to ever witness a transition. Callers supply the
// two signed endpoints of the open interval `(lower, upper)` that
// the runtime would otherwise evaluate, plus `precision_ticks` — the
// number of simulation time ticks that make up one unit of
// simulation precision. Returns true only when the interval spans at
// least two units of simulation precision, reflecting the LRM's
// statement that narrower windows cannot yield timing violations
// because no sample point falls strictly between the two endpoints.
// An empty or inverted interval (`upper <= lower`) returns false.
bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks);

// §31.9.1: one step of the resolution procedure for a mutually
// inconsistent set of negative timing-check limits. `limits` is an
// in/out vector of the signed limits participating in the solve.
// The helper locates the negative entry closest to zero — i.e. the
// smallest negative in magnitude, the conservative "least change"
// choice when multiple negatives are tied the earliest such entry
// is selected for determinism — and rewrites it to zero. Returns
// true when a rewrite happened, false when the vector contained no
// negatives and the caller has therefore already reached a solvable
// state. Callers drive the outer loop themselves: after each rewrite
// they re-run their delay solver and invoke this helper again if
// the inconsistency persists. The LRM guarantees the loop terminates
// because in the worst case every negative limit ends up zeroed and
// no delays are required at all.
bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits);

// §31.9.2: which of the two sides of a $setuphold or $recrem check a
// post-notifier condition argument gates. The condition pairs up with
// the delayed signal whose transition it qualifies, and which side that
// is depends on the signed setup/hold limits: with both non-negative
// the equivalent $setup + $hold pair both consult the condition
// (kBoth); a negative setup collapses the window entirely onto the
// hold-like side so only one delayed signal is in play (kData for the
// timecheck, kRef for the timestamp); a negative hold mirrors that on
// the setup-like side (kRef for the timecheck, kData for the
// timestamp). kNone is reserved for the mutually inconsistent
// both-negative configuration, which §31.9.1's resolver must rewrite
// before the role is meaningful.
enum class NegativeTimingConditionRole : uint8_t {
  kData,
  kRef,
  kBoth,
  kNone,
};

// §31.9.2: classify which side the timestamp_condition argument of a
// $setuphold or $recrem invocation is associated with. The timestamp
// condition gates the delayed signal that transitions first: the data
// signal in the setup-like direction and the reference signal in the
// hold-like direction. With both limits non-negative both decomposed
// checks fire, so the condition gates both sides (kBoth). A single
// negative on either limit collapses the window to one direction and
// the role narrows to that single side. Both-negative is flagged as
// kNone because §31.9.1's resolver has not yet chosen which limit to
// zero.
NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

// §31.9.2: classify which side the timecheck_condition argument of a
// $setuphold or $recrem invocation is associated with. Symmetric to
// TimestampConditionRole, but gates the delayed signal that transitions
// second: reference in the setup-like direction and data in the
// hold-like direction. Negative setup therefore lands on data (the
// post-ref window) and negative hold on reference (the pre-ref window).
NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

// =============================================================================
// SDF annotation entry (§32)
// =============================================================================

struct SdfAnnotation {
  std::string sdf_file;
  std::string scope;  // Module instance scope
};

// =============================================================================
// SpecifyManager: manages path delays, timing checks, and SDF (§30-32)
// =============================================================================

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay);
  void AddTimingCheck(TimingCheckEntry check);
  void AnnotateSdf(SdfAnnotation annotation);

  uint64_t GetPathDelay(std::string_view src, std::string_view dst) const;
  const std::vector<PathDelay>& GetPathDelays() const { return path_delays_; }

  const std::vector<TimingCheckEntry>& GetTimingChecks() const {
    return timing_checks_;
  }

  const std::vector<SdfAnnotation>& GetSdfAnnotations() const {
    return sdf_annotations_;
  }

  bool HasPathDelay(std::string_view src, std::string_view dst) const;
  bool CheckSetupViolation(std::string_view ref, uint64_t ref_time,
                           std::string_view data, uint64_t data_time) const;
  bool CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;
  // §31.3.3: $setuphold combines the $setup and $hold windows in a single
  // check whose active branch is selected by which event occurred first.
  // `limit` holds the setup limit and `limit2` holds the hold limit on the
  // stored TimingCheckEntry.
  //
  // §31.9: when the stored entry has `negative_timing_check_enabled` set,
  // the effective setup / hold limits are taken with sign from
  // `signed_limit` and `signed_limit2` and the check evaluates the open
  // interval (ref - setup, ref + hold). Negative limits therefore shift
  // the interval off the reference edge rather than straddling it, and
  // the two kinds ($setuphold and $recrem) agree on one interval
  // formula so they behave identically for any given pair of signed
  // values.
  bool CheckSetupholdViolation(std::string_view ref, uint64_t ref_time,
                               std::string_view data, uint64_t data_time) const;
  // §31.3.4: $removal. `ref`/`ref_time` identify the reference_event (the
  // timecheck event, typically a control signal); `data`/`data_time` identify
  // the data_event (the timestamp event, typically a clock).
  bool CheckRemovalViolation(std::string_view ref, uint64_t ref_time,
                             std::string_view data, uint64_t data_time) const;
  // §31.3.5: $recovery. `ref`/`ref_time` identify the reference_event (the
  // timestamp event, typically a control signal); `data`/`data_time` identify
  // the data_event (the timecheck event, typically a clock).
  bool CheckRecoveryViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;
  // §31.3.6: $recrem combines the $recovery and $removal windows in a single
  // check whose active branch is selected by which event occurred first.
  // `limit` holds the recovery_limit and `limit2` holds the removal_limit on
  // the stored TimingCheckEntry (matching the invocation argument order
  // `$recrem(ref, data, recovery_limit, removal_limit)`).
  //
  // §31.9: when `negative_timing_check_enabled` is set on the stored
  // entry, `signed_limit` and `signed_limit2` supply the signed
  // recovery / removal limits and the check evaluates the same open
  // interval (ref - recovery, ref + removal) as the $setuphold path.
  // The shared formula is what guarantees the LRM's requirement that
  // $setuphold and $recrem behave identically with respect to negative
  // values.
  bool CheckRecremViolation(std::string_view ref, uint64_t ref_time,
                            std::string_view data, uint64_t data_time) const;
  // §31.4.1: $skew. `ref`/`ref_time` identify the reference_event (the
  // timestamp event); `data`/`data_time` identify the data_event (the
  // timecheck event). A violation is reported when the data event follows
  // the reference event by strictly more than `limit`. Callers should invoke
  // this helper once per data event with the most recent ref_time.
  bool CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;
  // §31.4.2: $timeskew. `ref`/`ref_time` identify the reference_event
  // (timestamp event); `data`/`data_time` identify the data_event
  // (timecheck event). The violation predicate is the strict inequality
  //   (timecheck time) - (timestamp time) > limit
  // which also implements §31.4.2's two carve-outs in one expression: the
  // simultaneous-transition rule (no violation when both events coincide,
  // even at zero limit) and the exact-expiration rule (no violation when a
  // new timestamp event lands precisely at the elapsed-limit boundary).
  bool CheckTimeskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data,
                              uint64_t data_time) const;
  // §31.4.3: $fullskew. `ref`/`ref_time` identify the reference_event,
  // `data`/`data_time` identify the data_event; either may transition
  // first. The active window uses `limit` (limit 1) when the reference
  // transitions first and `limit2` (limit 2) when the data event
  // transitions first, consistent with §31.4.3's direction-dependent
  // definition. The violation predicate is the strict inequality
  //   (timecheck time) - (timestamp time) > limit
  // which also folds in §31.4.3's simultaneous-transition carve-out
  // (no violation when both events coincide, even at zero limit) and
  // the exact-expiration rule for a new timestamp event.
  bool CheckFullskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data,
                              uint64_t data_time) const;
  // §31.4.4: $width. `ref`/`ref_time` identify the reference event
  // (timestamp event on the reference signal); `data_time` is the time
  // of the derived data event — the opposite edge on the same reference
  // signal. The violation predicate is the two-sided strict inequality
  //   threshold < (timecheck time) - (timestamp time) < limit
  // The strict upper bound encodes "pulse width >= limit avoids a
  // violation" and the strict lower bound implements the glitch
  // carve-out (pulses at or below `threshold` are ignored). The LRM also
  // forbids the reference and data events from occurring at the same
  // simulation time; callers passing a non-greater `data_time` see no
  // violation.
  bool CheckWidthViolation(std::string_view ref, uint64_t ref_time,
                           uint64_t data_time) const;
  // §31.4.5: $period. `ref`/`ref_time` identify the reference event
  // (timestamp event on the reference signal); `data_time` is the time
  // of the derived data event — the same-edge transition on the same
  // reference signal. The violation predicate is the strict inequality
  //   (timecheck time) - (timestamp time) < limit
  // which witnesses a period shorter than `limit`. A non-greater
  // `data_time` is treated as "no period closed yet" so callers need not
  // pre-filter.
  bool CheckPeriodViolation(std::string_view ref, uint64_t ref_time,
                            uint64_t data_time) const;
  // §31.4.6: $nochange. `ref`/`leading_ref_time`/`trailing_ref_time`
  // identify the three-transition reference event (the leading edge
  // opens the time window, the trailing edge closes it); `data`/
  // `data_time` identify the data event. The violation predicate is
  //   (leading_ref_time - start_edge_offset) < data_time
  //     < (trailing_ref_time + end_edge_offset)
  // with strict inequalities on both endpoints, folding in §31.4.6's
  // "end points of the time window are not included" rule and the
  // example's simultaneous-edge carve-out when offsets are zero.
  // `start_edge_offset` and `end_edge_offset` on the stored entry are
  // signed: a positive value extends the window past the reference
  // edge, and a negative value shrinks the window inward.
  bool CheckNochangeViolation(std::string_view ref, uint64_t leading_ref_time,
                              uint64_t trailing_ref_time,
                              std::string_view data, uint64_t data_time) const;

  uint32_t PathDelayCount() const {
    return static_cast<uint32_t>(path_delays_.size());
  }
  uint32_t TimingCheckCount() const {
    return static_cast<uint32_t>(timing_checks_.size());
  }

 private:
  using PathKey = std::pair<std::string, std::string>;
  struct PairHash {
    size_t operator()(const PathKey& p) const {
      auto h1 = std::hash<std::string>{}(p.first);
      auto h2 = std::hash<std::string>{}(p.second);
      return h1 ^ (h2 << 1);
    }
  };

  std::vector<PathDelay> path_delays_;
  std::unordered_map<PathKey, size_t, PairHash> path_index_;
  std::vector<TimingCheckEntry> timing_checks_;
  std::vector<SdfAnnotation> sdf_annotations_;
};

}  // namespace delta
