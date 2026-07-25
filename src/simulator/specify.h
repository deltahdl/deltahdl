#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

struct PathDelay {
  std::string src_port;
  std::string dst_port;
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;

  std::string condition;

  bool is_ifnone = false;
  uint8_t delay_count = 1;
  uint64_t delays[12] = {};

  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

uint64_t ClampPathDelay(int64_t signed_value);

void ExpandTransitionDelays(PathDelay& pd);

class SimContext;

// §30.5.1: turn a parsed module path assignment into the runtime PathDelay that
// carries its transition delays. Each listed delay expression is evaluated in
// `ctx`; a single value is the typical delay and a min:typ:max triple selects a
// member per the context's delay mode. A delay that evaluates to a negative
// value is treated as zero, and the resulting one/two/three/six/twelve values
// are distributed across all twelve transition slots per Table 30-2.
PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena);

struct PathCandidate {
  const PathDelay* path = nullptr;
  uint64_t last_transition_time = 0;
  bool condition_true = true;
};

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot);

// §30.4.4.1: decide whether a state-dependent module path's conditional
// expression makes the path active. The path is active when the condition is
// true (1); an x or z result is taken as true; a multi-bit result is
// represented by its LSB, so the caller passes the least-significant 4-state
// word. The returned value is what PathCandidate::condition_true holds.
bool StateDependentPathConditionEnables(Logic4Word condition_lsb);

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum);

enum class PulseClassification : uint8_t {
  kPropagate,
  kForceX,
  kReject,
};

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit);

// §30.7.4.1: the pulse-filtering style. It selects only WHEN the leading edge
// of a pulse that is being filtered to x transitions; on-event is the default.
enum class PulseStyle : uint8_t {
  kOnEvent,
  kOnDetect,
};

// §30.7.4.1: the leading-edge transition time when a pulse is filtered to x.
// Both styles turn the leading edge into a transition to x and the trailing
// edge into a transition from x. On-event (the default) leaves the leading
// transition at its already-scheduled time; on-detect advances it to the moment
// the pulse is detected. The trailing edge time is unchanged under either
// style.
uint64_t FilteredPulseLeadingXTime(PulseStyle style, uint64_t detect_time,
                                   uint64_t scheduled_leading_time);

// §30.7.4.2: whether a cancelled (negative-width) pulse is made visible as x.
// noshowcancelled (the default) silently cancels the leading edge;
// showcancelled drives the output to x for the duration of the cancelled pulse.
enum class ShowCancelled : uint8_t {
  kNoshowcancelled,
  kShowcancelled,
};

// §30.7.4.2: a pulse is negative when its trailing edge is scheduled earlier
// than its leading edge, which happens on a module path with unequal delays and
// yields a negative width.
bool IsNegativePulse(uint64_t leading_time, uint64_t trailing_time);

// §30.7.4.2: how a negative pulse resolves at a module path output.
struct NegativePulseSchedule {
  // noshowcancelled -> false: the leading edge is cancelled, and when the pulse
  // initial and final states match no transition emerges at all.
  // showcancelled -> true: schedule the leading edge to x and the trailing edge
  // from x.
  bool force_x;
  // Only meaningful when force_x: the time of the transition to x. With the
  // on-event style the schedule to x replaces the leading edge at its already
  // scheduled time; with on-detect it is made immediately upon detection.
  uint64_t x_time;
};

// §30.7.4.2: resolve a negative pulse given the showcancelled mode and the
// pulse-filtering style. The leading-x timing reuses the §30.7.4.1 rule.
NegativePulseSchedule ScheduleNegativePulse(ShowCancelled mode,
                                            PulseStyle style,
                                            uint64_t detect_time,
                                            uint64_t scheduled_leading_time);

void InitDefaultPulseLimits(PathDelay& pd);

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error);

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct);

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error);

struct TimingCheckEntry {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  uint64_t limit = 0;
  uint64_t limit2 = 0;

  bool negative_timing_check_enabled = false;
  int64_t signed_limit = 0;
  int64_t signed_limit2 = 0;

  uint64_t threshold = 0;

  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  std::string notifier;

  std::string condition;
};

// §31.4.1: the $skew check is event-based and stateful. Reference- and data-
// signal transitions are fed in time order; the check remembers the most
// recent reference event and, on each data event, reports a violation when the
// data event falls more than `limit` time units after that reference. Unlike
// the stateless CheckSkewViolation predicate, this models the temporal rules
// the LRM states for $skew:
//   - event-based: only a data event can produce a violation, so a reference
//     event with no following data event never reports one;
//   - the wait for a data event is open-ended -- an arbitrarily late data
//     event is still checked;
//   - a second reference event arriving before any data event supersedes the
//     first (its wait is cancelled and a new one begins);
//   - checking never stops after a reference: every later data event beyond
//     the limit reports a violation, not just the first.
class SkewChecker {
 public:
  explicit SkewChecker(uint64_t limit) : limit_(limit) {}

  // A reference-signal transition at `time`. Opens (or, if one is already
  // open, restarts) the wait for a data event.
  void ReferenceEvent(uint64_t time) {
    reference_time_ = time;
    has_reference_ = true;
  }

  // A data-signal transition at `time`. Returns true iff it violates the skew
  // limit relative to the most recent reference event. A data event with no
  // preceding reference, or one simultaneous with or earlier than the
  // reference, never violates.
  bool DataEvent(uint64_t time) const {
    if (!has_reference_) return false;
    if (time <= reference_time_) return false;
    return time - reference_time_ > limit_;
  }

 private:
  uint64_t limit_;
  uint64_t reference_time_ = 0;
  bool has_reference_ = false;
};

// §31.4.2: $timeskew is stateful and, unlike $skew, defaults to *timer-based*
// detection; the event_based_flag switches it to *event-based* ($skew-like)
// detection. This models the dormancy rules stated in the LRM that the
// per-event ReportsTimeskewViolation oracle and the stateless
// CheckTimeskewViolation predicate do not capture:
//   timer-based (default -- event_based_flag clear):
//     - the violation is reported when the limit elapses after the reference
//       with no intervening data event (Timeout), after which the check is
//       dormant and reports nothing until the next reference;
//     - a data event within (or at) the limit reports nothing and also turns
//       the check dormant immediately, so the pending timeout never fires;
//   event-based (event_based_flag set): a data event beyond the limit reports,
//     just like $skew, with the twist keyed to remain_active_flag --
//     - remain_active_flag set (both flags): the check stays armed and reports
//       every later violation, exactly like $skew;
//     - remain_active_flag clear (only event_based_flag): the check turns
//       dormant after its first reported violation;
//   in either mode a conditioned reference whose condition is false turns the
//   check dormant unless remain_active_flag is set (then the event is ignored
//   and any open window stands), while a reference whose condition holds always
//   re-arms the check.
class TimeskewChecker {
 public:
  TimeskewChecker(uint64_t limit, bool event_based_flag,
                  bool remain_active_flag)
      : limit_(limit),
        event_based_(event_based_flag),
        remain_active_(remain_active_flag) {}

  // A reference (timestamp) transition at `time`. `condition_holds` is false
  // only for a conditioned reference event whose condition evaluated false.
  void ReferenceEvent(uint64_t time, bool condition_holds = true) {
    if (condition_holds) {
      reference_time_ = time;
      armed_ = true;
      return;
    }
    // Conditioned reference with a false condition: a set remain_active_flag
    // discards the event and leaves the window untouched; otherwise the check
    // goes dormant.
    if (!remain_active_) armed_ = false;
  }

  // A data (timecheck) transition at `time`. Returns true iff it reports a
  // violation now. A data event with no armed reference, or one simultaneous
  // with or earlier than the reference, never violates.
  bool DataEvent(uint64_t time) {
    if (!armed_) return false;
    if (time <= reference_time_) return false;
    uint64_t elapsed = time - reference_time_;
    if (event_based_) {
      if (elapsed <= limit_) return false;
      if (!remain_active_) armed_ = false;  // dormant after the first violation
      return true;
    }
    // Timer-based: a data event seen while still armed is necessarily within
    // (or at) the limit -- a later one cannot arrive first because the timeout
    // fires at reference+limit. It reports nothing and turns the check dormant.
    armed_ = false;
    return false;
  }

  // Timer-based only: the limit has elapsed after the reference with no data
  // event. Reports the violation once, then the check is dormant until the next
  // reference. Always a no-op in event-based mode.
  bool Timeout() {
    if (event_based_ || !armed_) return false;
    armed_ = false;
    return true;
  }

 private:
  uint64_t limit_;
  bool event_based_;
  bool remain_active_;
  uint64_t reference_time_ = 0;
  bool armed_ = false;
};

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag);

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag);

// Effect of a fresh timestamp event on a $fullskew check (§31.4.3
// remain_active_flag semantics; identical in timer-based and event-based
// modes).
enum class FullskewWindowAction : uint8_t {
  kReplaceWindow,  // condition holds: a new window supersedes the open one /
                   // re-arms
  kIgnore,  // condition false but remain_active_flag set: event has no effect
  kGoDormant,  // condition false and remain_active_flag clear: check goes
               // dormant
};

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag);

Logic4Word ToggleNotifierOnViolation(Logic4Word current);

enum class TimingCheckConditionKind : uint8_t {
  kPlain,
  kNegate,
  kEq,
  kCaseEq,
  kNeq,
  kCaseNeq,
};

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind);

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit);

// §31.7: the scalar_timing_check_condition form (Syntax 31-16) a parsed `&&&`
// condition matches, plus -- for the equality/inequality forms -- the value of
// the scalar_constant on the right-hand side. `scalar_constant_bit` is only
// meaningful when `kind` is one of the four comparison forms; for the plain and
// `~` forms it is unused.
struct TimingCheckConditionClass {
  TimingCheckConditionKind kind = TimingCheckConditionKind::kPlain;
  uint8_t scalar_constant_bit = 0;
};

// §31.7: bridge the parsed `&&&` condition expression to the enable semantics.
// The raw condition Expr stored by the parser (TimingCheckDecl::ref_condition /
// data_condition) is inspected here to recover which of the six
// scalar_timing_check_condition forms it is, so its deterministic vs
// nondeterministic treatment can be applied by TimingCheckConditionEnables. A
// null expression -- an unconditioned timing-check event -- is reported as the
// plain form. `~ expression` maps to the negate form; the ==, ===, !=, and !==
// binary forms map to their respective comparison kinds and carry the LSB of
// the scalar_constant operand; any other expression is the plain form.
TimingCheckConditionClass ClassifyTimingCheckCondition(const Expr* condition);

bool IsSingleSignalTimingCheck(TimingCheckKind kind);

enum class TimingCheckVectorMode : uint8_t {
  kSingle,
  kPerBit,
};

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode);

// §31.8: with the optional per-bit expansion enabled, a vector-signal timing
// check becomes an independent single-bit check for each bit, but only a bit
// that actually transitions reports a violation. Given a vector's value before
// and after an event, this counts the bit positions that changed within `width`
// -- the number of violations the expansion yields, which is generally fewer
// than the checks TimingCheckExpandedCount creates. In the LRM DFF example DAT
// changes in six of its eight bits, so its eight per-bit checks yield six
// violations.
uint32_t VectorTransitionViolationCount(uint64_t before, uint64_t after,
                                        uint32_t width);

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind);

struct AdjustedNegativeTimingLimit {
  uint64_t limit;
  bool warn;
};

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit);

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks);

// §31.9.1 requirement (b): which data value is latched given the
// negative-timing violation window, whose end points are excluded exactly as
// requirement (a) excludes them for violation detection.
// `window_lower`/`window_upper` are the reference-centered bounds (the same
// interval NegativeTimingWindowViolated uses); `data_transition_time` is when
// the data settled from `old_value` to `new_value`. If the data settled at or
// before the window opens, the new value is stable across the whole interior
// and is latched; otherwise the old value is the stable one -- and for a
// transition that lands inside the window this is the stale value that is
// incorrectly clocked in (LRM Example 1).
uint64_t LatchedNegativeTimingWindowValue(int64_t window_lower,
                                          int64_t window_upper,
                                          int64_t data_transition_time,
                                          uint64_t old_value,
                                          uint64_t new_value);

// §31.9.1: a timing check creates implicit delayed copies of its reference and
// data signals only when a negative setup or hold value is present and no
// delayed signals were explicitly declared within the check. Explicit delayed
// signals, when declared, are used instead (and can drive model behavior);
// implicit ones are created solely for internal evaluation.
bool ImplicitDelayedSignalsRequired(bool negative_setup_or_hold_present,
                                    bool explicit_delayed_signals_declared);

// §31.9.1: when a timing-check signal is delayed by more than the propagation
// delay from that signal to an output, the output can no longer change at its
// nominal propagation delay; it instead transitions when the delayed signal
// changes, so its effective specify path delay becomes the applied timing-check
// delay. The effective output delay is therefore the larger of the propagation
// delay and the applied timing-check-signal delay.
uint64_t EffectiveOutputDelayWithTimingCheckSignalDelay(
    uint64_t propagation_delay, uint64_t timing_check_signal_delay);

// §31.9.1 (Examples 2-3): the single delayed copy resolved for one referenced
// timing-check signal. `delayed_name` is the explicit delayed-signal name when
// one was declared, otherwise empty for an implicit copy.
struct ResolvedDelayedSignal {
  std::string signal;
  std::string delayed_name;
  bool is_explicit = false;
};

// §31.9.1 (Examples 2-3): reduce the per-check delayed-signal declarations to
// one delayed copy per distinct referenced signal. `refs` lists, in check
// order, each (referenced-signal, explicit-delayed-name) pair -- an empty
// delayed name meaning that check declared none. A signal referenced by several
// checks yields a single shared copy rather than one per check; and if any
// referencing check declares an explicit delayed signal, that explicit copy is
// used for every such check and no implicit copy is created (an explicit
// declaration in one check is honored even when another check leaves it
// implicit). The first explicit name seen for a signal wins. Entries are
// returned in order of first appearance.
std::vector<ResolvedDelayedSignal> ResolveDelayedSignals(
    const std::vector<std::pair<std::string, std::string>>& refs);

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits);

enum class NegativeTimingConditionRole : uint8_t {
  kData,
  kRef,
  kBoth,
  kNone,
};

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold);

bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool undelayed_original_violation);

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled);

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active);

struct SdfAnnotation {
  std::string sdf_file;
  std::string scope;
};

struct SpecparamValue {
  std::string name;
  uint64_t value = 0;
};

struct InterconnectDelay {
  std::string src_port;
  std::string dst_port;
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t delays[12] = {};
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

struct SdfTcAnnotation {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  std::string condition;
  uint64_t limit = 0;
  uint64_t limit2 = 0;
  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  bool set_limit = false;
  bool set_limit2 = false;
  bool set_start_edge_offset = false;
  bool set_end_edge_offset = false;
};

// §30.7.1: a PATHPULSE$ pulse-control specparam gathered from a specify block.
// `input`/`output` name the module path terminals; when both are empty the
// specparam is not path-specific and applies to every module path in the
// module. `reject` is the reject limit and, when `has_error` is set, `error` is
// the separately given error limit; otherwise the reject limit also serves as
// the error limit.
struct PulseControlSpecparam {
  std::string_view input;
  std::string_view output;
  uint64_t reject = 0;
  bool has_error = false;
  uint64_t error = 0;
};

// An SDF PATHPULSE pulse-limit specification applied to the module path that
// runs from src to dst. reject/error are the reject and error pulse limits;
// when has_error is false the reject limit also serves as the error limit. When
// is_percent is set the limits are percentages of the path delay rather than
// absolute time values.
struct SdfPulseLimitSpec {
  std::string_view src;
  std::string_view dst;
  uint64_t reject = 0;
  uint64_t error = 0;
  bool has_error = false;
  bool is_percent = false;
};

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay, bool preserve_pulse_limits = false);

  void IncrementPathDelay(const PathDelay& delta);
  void AddTimingCheck(TimingCheckEntry check);

  void AnnotateSdfTimingCheck(const SdfTcAnnotation& annotation);

  void AnnotateSdf(SdfAnnotation annotation);
  void SetSpecparamValue(SpecparamValue spec);

  void IncrementSpecparamValue(SpecparamValue delta);
  void AddInterconnectDelay(InterconnectDelay delay);

  void IncrementInterconnectDelay(const InterconnectDelay& delta);

  void RegisterSpecparamReevaluation(std::string name,
                                     std::function<void(uint64_t)> reevaluate);

  void AddSdfPulseLimit(const SdfPulseLimitSpec& spec);

  // §30.7.1: apply the specify block's PATHPULSE$ pulse-control specparams to
  // the module's path delays. A non-path-specific specparam sets the limits of
  // every path; a path-specific specparam overrides only the path it names and
  // takes precedence over any non-path-specific one, regardless of the order in
  // which the specparams were declared.
  void ResolvePulseControlSpecparams(
      const std::vector<PulseControlSpecparam>& specs);

  void IncrementSdfPulseLimit(std::string_view src, std::string_view dst,
                              int64_t reject_delta, bool has_error,
                              int64_t error_delta);

  void SetGlobalPulseLimitPercents(uint8_t reject_pct, uint8_t error_pct);

  uint8_t RejectPulseLimitPercent() const { return reject_pulse_pct_; }
  uint8_t ErrorPulseLimitPercent() const { return error_pulse_pct_; }

  // §30.7.4.1: record the pulse-filtering style a specify block pulsestyle
  // declaration selects for a module path output.
  void SetPathOutputPulseStyle(std::string output, PulseStyle style);

  // §30.7.4.1: select a pulse-filtering style globally through the on-event/
  // on-detect invocation option. It takes precedence over any specify block
  // pulse style declaration.
  void SetGlobalPulseStyle(PulseStyle style);

  // §30.7.4.1: resolve the effective pulse-filtering style for a module path
  // output. A global invocation-option style wins over a specify block
  // declaration; absent both, the default is on-event.
  PulseStyle ResolvePulseStyle(std::string_view output) const;

  // §30.7.4.2: record the showcancelled mode a specify block showcancelled/
  // noshowcancelled declaration selects for a module path output.
  void SetPathOutputShowCancelled(std::string output, ShowCancelled mode);

  // §30.7.4.2: select a showcancelled mode globally through the showcancelled/
  // noshowcancelled invocation option. It takes precedence over any specify
  // block showcancelled declaration.
  void SetGlobalShowCancelled(ShowCancelled mode);

  // §30.7.4.2: resolve the effective showcancelled mode for a module path
  // output. A global invocation-option mode wins over a specify block
  // declaration; absent both, the default is noshowcancelled.
  ShowCancelled ResolveShowCancelled(std::string_view output) const;

  const std::vector<SpecparamValue>& GetSpecparamValues() const {
    return specparam_values_;
  }
  const std::vector<InterconnectDelay>& GetInterconnectDelays() const {
    return interconnect_delays_;
  }

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

  bool CheckSetupholdViolation(std::string_view ref, uint64_t ref_time,
                               std::string_view data, uint64_t data_time) const;

  bool CheckRemovalViolation(std::string_view ref, uint64_t ref_time,
                             std::string_view data, uint64_t data_time) const;

  bool CheckRecoveryViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckRecremViolation(std::string_view ref, uint64_t ref_time,
                            std::string_view data, uint64_t data_time) const;

  bool CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;

  bool CheckTimeskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckFullskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckWidthViolation(std::string_view ref, uint64_t ref_time,
                           uint64_t data_time) const;

  bool CheckPeriodViolation(std::string_view ref, uint64_t ref_time,
                            uint64_t data_time) const;

  bool CheckNochangeViolation(std::string_view ref, uint64_t leading_ref_time,
                              uint64_t trailing_ref_time, std::string_view data,
                              uint64_t data_time) const;

  uint32_t PathDelayCount() const {
    return static_cast<uint32_t>(path_delays_.size());
  }
  uint32_t TimingCheckCount() const {
    return static_cast<uint32_t>(timing_checks_.size());
  }

 private:
  std::vector<PathDelay> path_delays_;
  std::vector<TimingCheckEntry> timing_checks_;
  std::vector<SdfAnnotation> sdf_annotations_;

  std::vector<SpecparamValue> specparam_values_;
  std::unordered_map<std::string, size_t> specparam_index_;
  std::vector<InterconnectDelay> interconnect_delays_;

  std::vector<std::pair<std::string, std::function<void(uint64_t)>>>
      specparam_reevaluators_;

  uint8_t reject_pulse_pct_ = 100;
  uint8_t error_pulse_pct_ = 100;

  std::unordered_map<std::string, PulseStyle> path_output_pulse_styles_;
  bool has_global_pulse_style_ = false;
  PulseStyle global_pulse_style_ = PulseStyle::kOnEvent;

  std::unordered_map<std::string, ShowCancelled> path_output_showcancelled_;
  bool has_global_showcancelled_ = false;
  ShowCancelled global_showcancelled_ = ShowCancelled::kNoshowcancelled;
};

}  // namespace delta
