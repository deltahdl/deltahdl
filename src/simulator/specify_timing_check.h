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
#include "simulator/specify_path_delay.h"

namespace delta {

class SimContext;
class Scheduler;

struct TimingCheckEntry {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;

  // The hierarchical prefix of the module instance whose specify block declared
  // this check, ending in a `.` and empty for a module elaborated as a top.
  // §31.2 puts a system timing check inside a specify block and §30.3 puts that
  // block inside a module declaration, so two instances of one cell declare
  // checks whose ref_signal and data_signal are spelled identically; this is
  // what tells them apart. It is the same string PathDelay::inst_prefix
  // (simulator/specify_path_delay.h) carries, which is what every variable of
  // an instantiated module is named under.
  std::string inst_prefix;

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

  // §31.7: the `&&&` condition each of the check's two timing_check_events was
  // declared with, held as the expression the parser built and null for an
  // event written without one. The `condition` text above is rendered for
  // §32.4.1's SDF COND matching and cannot answer whether a condition holds
  // now, which is what decides whether an event that just happened is a
  // conditioned event at all. PathDelay::condition_expr
  // (simulator/specify_path_delay.h) stands beside PathDelay::condition for the
  // same reason. The two are read through TimingCheckEventEnabled
  // (simulator/timing_check_driver_internal.h), which applies §31.7's
  // deterministic and nondeterministic rules to the conditioning signal.
  const Expr* ref_condition_expr = nullptr;
  const Expr* data_condition_expr = nullptr;
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

// §31.7: the conditioning signal of a parsed `&&&` condition -- the operand
// whose value the clause reads, which is not the value of the condition
// expression as a whole. Syntax 31-16 writes a scalar_timing_check_condition as
// a bare `expression`, as `~ expression`, or as `expression <op>
// scalar_constant`, and in all six forms the conditioning signal is that
// `expression`: §31.7 states the rule over "an x value on the conditioning
// signal" and TimingCheckConditionEnables takes the signal's least significant
// bit, applying the `~` or the comparison itself. Evaluating the whole
// condition and passing that instead would apply the operator twice. Null for a
// null condition, which is an unconditioned event.
const Expr* TimingCheckConditioningSignal(const Expr* condition);

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

// §31.9.2: the four operand positions a negative timing check can carry. The
// reference and data signals are the transitioning events being checked; the
// timestamp_condition and timecheck_condition are the paired `&&&`-style
// enabling conditions (see §31.3.3 / §31.7).
enum class TimingCheckOperandKind : uint8_t {
  kReference,
  kData,
  kTimestampCondition,
  kTimecheckCondition,
};

// §31.9.2: implicit delayed copies are generated only for a check's reference
// and data signals; the timestamp_condition and timecheck_condition operands
// are never implicitly delayed by the simulator. A model that needs a delayed
// condition builds it explicitly as a function of the already-delayed
// reference/data signals. This predicate reports whether a given operand kind
// is eligible for an implicit delayed copy.
bool OperandGetsImplicitDelayedCopy(TimingCheckOperandKind kind);

// §31.9.3: a negative timing check delays its reference and data signals
// internally, so the violation is detected — and the notifier therefore
// toggled — only when the delayed signals, measured against the adjusted
// limits, are in violation. It is not toggled when the undelayed signals at the
// model inputs, measured against the original limits, would be in violation.
// This predicate reports whether the notifier should toggle given the two
// verdicts, keying solely off the delayed-adjusted one.
bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool undelayed_original_violation);

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled);

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active);

// §31.9.4: the invocation options that decide how a $setuphold or $recrem
// declaration carrying negative values behaves at run time. Negative-value
// handling is unavailable until its enabling option is selected; a separate
// option switches every timing check off.
struct TimingCheckInvocationOptions {
  bool negative_timing_checks = false;
  bool all_timing_checks_off = false;
};

// §31.9.4: whether a declaration's negative setup/hold values are honored. They
// are only when the check actually carries a negative value AND the enabling
// invocation option is in force (and all checks have not been switched off).
bool NegativeTimingCheckValuesAccepted(
    bool negative_value_present, const TimingCheckInvocationOptions& options);

// §31.9.4: the reference and data signals a $setuphold or $recrem check
// evaluates against once the invocation options are applied. With
// negative-value handling in force these are the internally delayed copies --
// the explicitly declared delayed-signal name where the check declares one,
// otherwise the implicit copy of §31.9.1 -- each carrying its requested delay.
// Without it (the enabling option absent, or all timing checks switched off)
// the delayed signals degenerate to copies of the originals: the original
// signal names, with no delay applied.
struct EffectiveDelayedSignals {
  std::string ref_signal;
  int64_t ref_delay = 0;
  std::string data_signal;
  int64_t data_delay = 0;
  bool are_copies_of_originals = false;
};

EffectiveDelayedSignals ResolveDelayedSignalsUnderOptions(
    const TimingCheckDecl& decl, int64_t requested_ref_delay,
    int64_t requested_data_delay, const TimingCheckInvocationOptions& options);

// §31.9.4: build the runtime entry for a parsed $setuphold or $recrem timing
// check, evaluating its limit expressions in `ctx` and gating negative-value
// handling on the invocation options. Without the enabling option a negative
// limit is not honored: the entry keeps the ordinary two-sided behavior of
// §31.3.3/§31.3.6 with the negative limit taken as zero.
TimingCheckEntry BuildTimingCheckUnderOptions(
    const TimingCheckDecl& decl, SimContext& ctx, Arena& arena,
    const TimingCheckInvocationOptions& options);

}  // namespace delta
