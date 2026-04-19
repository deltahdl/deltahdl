#include "simulator/specify.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>

namespace delta {

// =============================================================================
// §30.5.1 path-delay helpers
// =============================================================================

uint64_t ClampPathDelay(int64_t signed_value) {
  return signed_value < 0 ? 0u : static_cast<uint64_t>(signed_value);
}

void ExpandTransitionDelays(PathDelay& pd) {
  // §30.5.1 / Table 30-2 — populate non-x transition slots:
  //   [0]=0->1, [1]=1->0, [2]=0->z, [3]=z->1, [4]=1->z, [5]=z->0.
  switch (pd.delay_count) {
    case 1: {
      // Count 1: every basic transition uses the single value.
      const uint64_t t = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = t;
      break;
    }
    case 2: {
      // Count 2: trise covers 0->1/0->z/z->1; tfall covers 1->0/1->z/z->0.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      pd.delays[2] = trise;
      pd.delays[3] = trise;
      pd.delays[4] = tfall;
      pd.delays[5] = tfall;
      break;
    }
    case 3: {
      // Count 3: z-bound transitions share tz; trise/tfall keep their slots.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      const uint64_t tz = pd.delays[2];
      pd.delays[3] = trise;
      pd.delays[4] = tz;
      pd.delays[5] = tfall;
      break;
    }
    default:
      // Counts 6 and 12 arrive already laid out as Table 30-2 expects.
      break;
  }

  // §30.5.2 / Table 30-3 — derive x-transition slots from the non-x slots
  // using the pessimistic min/max rules. Skip when all twelve delays were
  // specified explicitly: in that case slots [6..11] are already authoritative.
  if (pd.delay_count == 12) return;
  pd.delays[6]  = std::min(pd.delays[2], pd.delays[0]);  // 0->x
  pd.delays[7]  = std::max(pd.delays[3], pd.delays[0]);  // x->1
  pd.delays[8]  = std::min(pd.delays[4], pd.delays[1]);  // 1->x
  pd.delays[9]  = std::max(pd.delays[5], pd.delays[1]);  // x->0
  pd.delays[10] = std::max(pd.delays[4], pd.delays[2]);  // x->z
  pd.delays[11] = std::min(pd.delays[3], pd.delays[5]);  // z->x
}

// =============================================================================
// §30.5.3 delay selection
// =============================================================================

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  if (candidates.empty()) return 0;
  // "Most recently" is a single timestamp across every candidate — condition
  // truth does not enter until the filter below, so an earlier-but-true path
  // stays inactive when a later input transitioned, regardless of its guard.
  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  bool have_active = false;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (c.last_transition_time != max_time) continue;
    if (!c.condition_true) continue;
    uint64_t d = c.path->delays[transition_slot];
    if (!have_active || d < best) {
      best = d;
      have_active = true;
    }
  }
  return have_active ? best : 0;
}

// =============================================================================
// §30.6 mixing module path delays and distributed delays
// =============================================================================

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum) {
  return std::max(module_path_delay, distributed_delay_sum);
}

// =============================================================================
// §30.7 pulse filtering
// =============================================================================

PulseClassification ClassifyPulse(uint64_t pulse_width, uint64_t reject_limit,
                                  uint64_t error_limit) {
  if (pulse_width >= error_limit) return PulseClassification::kPropagate;
  if (pulse_width >= reject_limit) return PulseClassification::kForceX;
  return PulseClassification::kReject;
}

void InitDefaultPulseLimits(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i];
    pd.error_limit[i] = pd.delays[i];
  }
}

// =============================================================================
// §30.7.1 PATHPULSE$ override
// =============================================================================

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  // A reject-only PATHPULSE$ collapses the X band to zero; mirror the reject
  // value into the error slot so ClassifyPulse can never observe has_error.
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

// =============================================================================
// §30.7.2 global pulse-limit invocation options
// =============================================================================

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  // Silently raise an under-specified error percentage so the resulting X
  // band is well-formed regardless of how the CLI options were supplied.
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

// =============================================================================
// §30.7.3 SDF pulse-limit annotation
// =============================================================================

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  // Mirror reject to the error slot when SDF omitted the error limit, so the
  // X band is never undefined for downstream classification.
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

// =============================================================================
// SpecifyManager
// =============================================================================

void SpecifyManager::AddPathDelay(PathDelay delay) {
  PathKey key{delay.src_port, delay.dst_port};
  path_index_[key] = path_delays_.size();
  path_delays_.push_back(std::move(delay));
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  timing_checks_.push_back(std::move(check));
}

void SpecifyManager::AnnotateSdf(SdfAnnotation annotation) {
  sdf_annotations_.push_back(std::move(annotation));
}

uint64_t SpecifyManager::GetPathDelay(std::string_view src,
                                      std::string_view dst) const {
  auto it = path_index_.find({std::string(src), std::string(dst)});
  if (it == path_index_.end()) return 0;
  return path_delays_[it->second].delays[0];
}

bool SpecifyManager::HasPathDelay(std::string_view src,
                                  std::string_view dst) const {
  return path_index_.count({std::string(src), std::string(dst)}) > 0;
}

bool SpecifyManager::CheckSetupViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         std::string_view data,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetup) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.1: window is (ref_time - limit, ref_time); endpoints are not
    // part of the violation region, so both inequalities are strict.
    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kHold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.2: window is [ref_time, ref_time + limit); only the end is
    // excluded from the violation region, so the lower bound is inclusive
    // and the upper bound is strict.
    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRemovalViolation(std::string_view ref,
                                           uint64_t ref_time,
                                           std::string_view data,
                                           uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRemoval) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.4: window is (ref_time - limit, ref_time); endpoints are not
    // part of the violation region, so both inequalities are strict.
    if (data_time < ref_time && ref_time - data_time < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckRecoveryViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecovery) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.5: window is [ref_time, ref_time + limit); only the end is
    // excluded from the violation region, so the lower bound is inclusive
    // and the upper bound is strict.
    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kRecrem) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.6: both limits zero — $recrem shall never issue a violation.
    if (check.limit == 0 && check.limit2 == 0) continue;
    if (data_time <= ref_time) {
      // Data event first (or simultaneous with the reference): the reference
      // is the timecheck event and the active window is
      //   (ref_time - removal_limit, ref_time]
      // The end of the window is included, so simultaneous events with a
      // positive removal_limit fall inside the violation region.
      if (ref_time - data_time < check.limit2) return true;
    } else {
      // Data event second: the reference is the timestamp event and the
      // active window is [ref_time, ref_time + recovery_limit), with only the
      // end excluded.
      if (data_time - ref_time < check.limit) return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.1: a violation occurs when the data event follows the reference
    // event by strictly more than `limit`. The strict inequality also
    // implements the zero-limit carve-out: when `limit` is zero, simultaneous
    // transitions produce `0 > 0` (false) and therefore do not violate.
    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckTimeskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kTimeskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.2: a violation is reported only when
    //   (timecheck time) - (timestamp time) > limit
    // The strict inequality folds in both carve-outs the LRM names
    // explicitly: simultaneous transitions never violate (even at zero
    // limit), and a new timestamp event arriving exactly at the elapsed
    // limit boundary does not violate.
    if (data_time > ref_time && data_time - ref_time > check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.3: the reference and data events can transition in either
    // order. When the reference transitions first it is the timestamp
    // event and the active window is bounded by limit 1; when the data
    // event transitions first the roles invert and limit 2 applies. The
    // strict inequality also encodes both carve-outs the LRM spells out:
    // simultaneous transitions never violate (even at zero limit), and a
    // new timestamp event arriving exactly at the elapsed boundary does
    // not violate.
    if (ref_time < data_time) {
      if (data_time - ref_time > check.limit) return true;
    } else if (data_time < ref_time) {
      if (ref_time - data_time > check.limit2) return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckWidthViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kWidth) continue;
    if (check.ref_signal != ref) continue;
    // §31.4.4: the data event is the opposite-edge transition on the
    // same reference signal, and the LRM states the two events shall
    // never occur at the same simulation time. Treat a non-greater
    // data_time as "no pulse closed yet" so callers need not pre-filter.
    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;
    // §31.4.4: violation predicate is the two-sided strict inequality
    //   threshold < elapsed < limit
    // The strict upper bound encodes "pulse width >= limit avoids a
    // violation"; the strict lower bound implements the glitch
    // carve-out that suppresses pulses at or below `threshold`.
    if (elapsed > check.threshold && elapsed < check.limit) return true;
  }
  return false;
}

bool SpecifyManager::CheckNochangeViolation(std::string_view ref,
                                            uint64_t leading_ref_time,
                                            uint64_t trailing_ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kNochange) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.4.6 violation predicate:
    //   (leading_ref - start_edge_offset) < data_time
    //     < (trailing_ref + end_edge_offset)
    // Offsets are signed — a positive start_edge_offset extends the
    // window earlier, and a negative one shrinks the window's start
    // later; the end_edge_offset is symmetric about the trailing edge.
    // Compute in int64_t so that negative offsets applied to a small
    // reference-edge time do not underflow.
    int64_t begin = static_cast<int64_t>(leading_ref_time) -
                    check.start_edge_offset;
    int64_t end = static_cast<int64_t>(trailing_ref_time) +
                  check.end_edge_offset;
    int64_t t = static_cast<int64_t>(data_time);
    // Strict inequalities encode §31.4.6's "end points of the time
    // window are not included" rule. The same exclusion also
    // implements the example's simultaneous-edge carve-out: when both
    // offsets are zero, a data event at the leading or trailing
    // reference edge lands exactly on an endpoint and does not
    // violate.
    if (begin < t && t < end) return true;
  }
  return false;
}

bool SpecifyManager::CheckPeriodViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kPeriod) continue;
    if (check.ref_signal != ref) continue;
    // §31.4.5: the data event is the same-edge transition on the same
    // reference signal, so it must follow the reference event. Treat a
    // non-greater data_time as "no period closed yet" so callers need
    // not pre-filter.
    if (data_time <= ref_time) continue;
    // §31.4.5 violation predicate:
    //   (timecheck time) - (timestamp time) < limit
    // The strict inequality encodes "elapsed >= limit avoids a
    // violation": a period at or above the limit is long enough.
    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time,
                              uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  // §31.4.3: events at or before the timestamp do not open a window.
  // This subsumes the simultaneous-transition carve-out (no violation
  // when both events coincide, even at zero limit).
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    // Event-based mode behaves like $skew for this window: only a
    // timecheck event past the limit witnesses a violation; a fresh
    // timestamp event silently begins a new window.
    return next_event_is_timecheck && elapsed > limit;
  }
  // Timer-based default: once the timer elapses any later event — a
  // timecheck or a fresh timestamp — witnesses a violation. Events
  // arriving exactly at the boundary do not violate, matching the
  // strict inequality and the explicit exact-expiration rule.
  return elapsed > limit;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  // Bail out for events that aren't strictly later than the reference
  // event. This subsumes §31.4.2's simultaneous-transition rule (no
  // violation when both events coincide, even at zero limit) and ignores
  // out-of-order inputs.
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    // Event-based mode: the check waits for a data event before
    // evaluating the predicate, mirroring $skew. A new reference event
    // simply re-arms the wait without producing a violation.
    return next_event_is_data && elapsed > limit;
  }
  // Timer-based default: the implicit timer fires at ref_time + limit.
  // Any observed event past that boundary witnesses a violation
  // (whether data or a fresh reference). Events arriving at exactly the
  // boundary do not violate, matching the strict inequality of the
  // §31.4.2 violation predicate and the explicit exact-expiration rule
  // for new timestamp events.
  return elapsed > limit;
}

// =============================================================================
// §31.6 notifier-update helper
// =============================================================================

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool pre_a = (current.aval & 1u) != 0u;
  const bool pre_b = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (pre_a && pre_b) {
    // z pre-state: preserve the dual-rail z encoding (aval=1, bval=1).
    result.aval = 1u;
    result.bval = 1u;
  } else if (pre_b) {
    // x pre-state: resolve to 0 so that successive violations drive the
    // observable 0→1→0 toggle sequence.
    result.aval = 0u;
    result.bval = 0u;
  } else if (pre_a) {
    // 1 pre-state flips to 0.
    result.aval = 0u;
    result.bval = 0u;
  } else {
    // 0 pre-state flips to 1.
    result.aval = 1u;
    result.bval = 0u;
  }
  return result;
}

// =============================================================================
// §31.7 conditioned-event enablement helpers
// =============================================================================

bool IsDeterministicTimingCheckCondition(TimingCheckConditionKind kind) {
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
    case TimingCheckConditionKind::kNegate:
    case TimingCheckConditionKind::kCaseEq:
    case TimingCheckConditionKind::kCaseNeq:
      return true;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kNeq:
      return false;
  }
  return false;
}

bool TimingCheckConditionEnables(TimingCheckConditionKind kind,
                                 Logic4Word conditioning_lsb,
                                 uint8_t scalar_constant_bit) {
  // Reduce the dual-rail encoding to the three cases §31.7 distinguishes:
  // known 0, known 1, or an unknown value. The LRM rule is phrased in
  // terms of the conditioning signal carrying an x, and the decision on x
  // is fixed by the operator's deterministic-vs-nondeterministic label —
  // regardless of what a literal four-valued evaluation of the operator
  // would produce.
  const bool known = (conditioning_lsb.bval & 1u) == 0u;
  if (!known) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const uint8_t bit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const uint8_t rhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return bit == 1u;
    case TimingCheckConditionKind::kNegate:
      return bit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return bit == rhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return bit != rhs;
  }
  return false;
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetuphold) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    // §31.3.3: both limits zero — $setuphold shall never issue a violation.
    if (check.limit == 0 && check.limit2 == 0) continue;
    if (data_time <= ref_time) {
      // Data event first (or simultaneous with the reference): the reference
      // is the timecheck event and the active window is
      //   (ref_time - setup_limit, ref_time]
      // The end of the window is included, so simultaneous events with a
      // positive setup limit fall inside the violation region.
      if (ref_time - data_time < check.limit) return true;
    } else {
      // Data event second: the reference is the timestamp event and the
      // active window is [ref_time, ref_time + hold_limit), with only the
      // end excluded.
      if (data_time - ref_time < check.limit2) return true;
    }
  }
  return false;
}

}  // namespace delta
