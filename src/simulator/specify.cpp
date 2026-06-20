#include "simulator/specify.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>

namespace delta {

uint64_t ClampPathDelay(int64_t signed_value) {
  return signed_value < 0 ? 0u : static_cast<uint64_t>(signed_value);
}

void ExpandTransitionDelays(PathDelay& pd) {
  switch (pd.delay_count) {
    case 1: {
      const uint64_t t = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = t;
      break;
    }
    case 2: {
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      pd.delays[2] = trise;
      pd.delays[3] = trise;
      pd.delays[4] = tfall;
      pd.delays[5] = tfall;
      break;
    }
    case 3: {
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      const uint64_t tz = pd.delays[2];
      pd.delays[3] = trise;
      pd.delays[4] = tz;
      pd.delays[5] = tfall;
      break;
    }
    default:

      break;
  }

  if (pd.delay_count == 12) return;
  pd.delays[6] = std::min(pd.delays[2], pd.delays[0]);
  pd.delays[7] = std::max(pd.delays[3], pd.delays[0]);
  pd.delays[8] = std::min(pd.delays[4], pd.delays[1]);
  pd.delays[9] = std::max(pd.delays[5], pd.delays[1]);
  pd.delays[10] = std::max(pd.delays[4], pd.delays[2]);
  pd.delays[11] = std::min(pd.delays[3], pd.delays[5]);
}

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  if (candidates.empty()) return 0;

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

bool StateDependentPathConditionEnables(Logic4Word condition_lsb) {
  // An unknown (x or z) condition counts as true; otherwise the path is active
  // only when the least-significant bit of the result is 1.
  const bool unknown = (condition_lsb.bval & 1u) != 0u;
  if (unknown) return true;
  return (condition_lsb.aval & 1u) != 0u;
}

uint64_t SelectEffectivePathDelay(uint64_t module_path_delay,
                                  uint64_t distributed_delay_sum) {
  return std::max(module_path_delay, distributed_delay_sum);
}

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

void ApplyPulseControlOverride(PathDelay& pd, uint64_t reject, bool has_error,
                               uint64_t error) {
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

void ApplyGlobalPulseLimits(PathDelay& pd, uint8_t reject_pct,
                            uint8_t error_pct) {
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

void ApplySdfPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                         uint64_t error) {
  const uint64_t effective_error = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = effective_error;
  }
}

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const bool sdf_is_nonconditional =
      delay.condition.empty() && !delay.is_ifnone;
  if (sdf_is_nonconditional) {
    bool matched = false;
    for (auto& existing : path_delays_) {
      if (existing.src_port == delay.src_port &&
          existing.dst_port == delay.dst_port) {
        std::string saved_cond = existing.condition;
        bool saved_ifnone = existing.is_ifnone;
        uint64_t saved_reject[12];
        uint64_t saved_error[12];
        if (preserve_pulse_limits) {
          for (int i = 0; i < 12; ++i) {
            saved_reject[i] = existing.reject_limit[i];
            saved_error[i] = existing.error_limit[i];
          }
        }
        existing = delay;
        existing.condition = std::move(saved_cond);
        existing.is_ifnone = saved_ifnone;
        if (preserve_pulse_limits) {
          for (int i = 0; i < 12; ++i) {
            existing.reject_limit[i] = saved_reject[i];
            existing.error_limit[i] = saved_error[i];
          }
        }
        matched = true;
      }
    }
    if (!matched) path_delays_.push_back(std::move(delay));
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      uint64_t saved_reject[12];
      uint64_t saved_error[12];
      if (preserve_pulse_limits) {
        for (int i = 0; i < 12; ++i) {
          saved_reject[i] = existing.reject_limit[i];
          saved_error[i] = existing.error_limit[i];
        }
      }
      existing = std::move(delay);
      if (preserve_pulse_limits) {
        for (int i = 0; i < 12; ++i) {
          existing.reject_limit[i] = saved_reject[i];
          existing.error_limit[i] = saved_error[i];
        }
      }
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

void SpecifyManager::IncrementPathDelay(const PathDelay& delta) {
  const bool sdf_is_nonconditional =
      delta.condition.empty() && !delta.is_ifnone;
  bool matched = false;
  if (sdf_is_nonconditional) {
    for (auto& existing : path_delays_) {
      if (existing.src_port == delta.src_port &&
          existing.dst_port == delta.dst_port) {
        for (int i = 0; i < 12; ++i) existing.delays[i] += delta.delays[i];
        matched = true;
      }
    }
  } else {
    for (auto& existing : path_delays_) {
      if (existing.src_port == delta.src_port &&
          existing.dst_port == delta.dst_port &&
          existing.condition == delta.condition &&
          existing.is_ifnone == delta.is_ifnone) {
        for (int i = 0; i < 12; ++i) existing.delays[i] += delta.delays[i];
        matched = true;
        break;
      }
    }
  }
  if (!matched) path_delays_.push_back(delta);
}

void SpecifyManager::IncrementInterconnectDelay(
    const InterconnectDelay& delta) {
  for (auto& existing : interconnect_delays_) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      existing.rise += delta.rise;
      existing.fall += delta.fall;
      for (int i = 0; i < 12; ++i) {
        existing.delays[i] += delta.delays[i];
      }
      return;
    }
  }
  interconnect_delays_.push_back(delta);
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  for (auto& existing : timing_checks_) {
    if (existing.kind == check.kind &&
        existing.ref_signal == check.ref_signal &&
        existing.ref_edge == check.ref_edge &&
        existing.data_signal == check.data_signal &&
        existing.data_edge == check.data_edge &&
        existing.condition == check.condition) {
      existing = std::move(check);
      return;
    }
  }
  timing_checks_.push_back(std::move(check));
}

void SpecifyManager::AnnotateSdfTimingCheck(const SdfTcAnnotation& a) {
  bool matched = false;
  for (auto& existing : timing_checks_) {
    if (existing.kind != a.kind) continue;
    if (existing.ref_signal != a.ref_signal) continue;
    if (existing.data_signal != a.data_signal) continue;
    if (a.ref_edge != SpecifyEdge::kNone && existing.ref_edge != a.ref_edge)
      continue;
    if (a.data_edge != SpecifyEdge::kNone && existing.data_edge != a.data_edge)
      continue;
    if (!a.condition.empty() && existing.condition != a.condition) continue;

    if (a.set_limit) existing.limit = a.limit;
    if (a.set_limit2) existing.limit2 = a.limit2;
    if (a.set_start_edge_offset)
      existing.start_edge_offset = a.start_edge_offset;
    if (a.set_end_edge_offset) existing.end_edge_offset = a.end_edge_offset;
    matched = true;
  }
  if (matched) return;

  TimingCheckEntry e;
  e.kind = a.kind;
  e.ref_signal = a.ref_signal;
  e.ref_edge = a.ref_edge;
  e.data_signal = a.data_signal;
  e.data_edge = a.data_edge;
  e.condition = a.condition;
  if (a.set_limit) e.limit = a.limit;
  if (a.set_limit2) e.limit2 = a.limit2;
  if (a.set_start_edge_offset) e.start_edge_offset = a.start_edge_offset;
  if (a.set_end_edge_offset) e.end_edge_offset = a.end_edge_offset;
  timing_checks_.push_back(std::move(e));
}

void SpecifyManager::AnnotateSdf(SdfAnnotation annotation) {
  sdf_annotations_.push_back(std::move(annotation));
}

void SpecifyManager::SetSpecparamValue(SpecparamValue spec) {
  std::string name = spec.name;
  uint64_t value = spec.value;
  auto it = specparam_index_.find(spec.name);
  if (it != specparam_index_.end()) {
    specparam_values_[it->second] = std::move(spec);
  } else {
    specparam_index_[spec.name] = specparam_values_.size();
    specparam_values_.push_back(std::move(spec));
  }

  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(value);
  }
}

void SpecifyManager::IncrementSpecparamValue(SpecparamValue delta) {
  std::string name = delta.name;
  uint64_t added = delta.value;
  uint64_t new_value = added;
  auto it = specparam_index_.find(name);
  if (it != specparam_index_.end()) {
    new_value = specparam_values_[it->second].value + added;
    specparam_values_[it->second].value = new_value;
  } else {
    specparam_index_[name] = specparam_values_.size();
    SpecparamValue stored;
    stored.name = name;
    stored.value = added;
    specparam_values_.push_back(std::move(stored));
  }
  for (const auto& reev : specparam_reevaluators_) {
    if (reev.first == name) reev.second(new_value);
  }
}

void SpecifyManager::RegisterSpecparamReevaluation(
    std::string name, std::function<void(uint64_t)> reevaluate) {
  specparam_reevaluators_.emplace_back(std::move(name), std::move(reevaluate));
}

void SpecifyManager::AddSdfPulseLimit(std::string_view src,
                                      std::string_view dst, uint64_t reject,
                                      bool has_error, uint64_t error,
                                      bool is_percent) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    if (is_percent) {
      uint64_t reject_pct = reject;
      uint64_t error_pct = has_error ? error : reject;
      if (error_pct < reject_pct) error_pct = reject_pct;
      for (int i = 0; i < 12; ++i) {
        pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
        pd.error_limit[i] = pd.delays[i] * error_pct / 100;
      }
    } else {
      ApplySdfPulseLimits(pd, reject, has_error, error);
    }

    for (int i = 0; i < 12; ++i) {
      if (pd.reject_limit[i] > pd.delays[i]) pd.reject_limit[i] = pd.delays[i];
      if (pd.error_limit[i] > pd.delays[i]) pd.error_limit[i] = pd.delays[i];
    }
  }
}

void SpecifyManager::IncrementSdfPulseLimit(std::string_view src,
                                            std::string_view dst,
                                            int64_t reject_delta,
                                            bool has_error,
                                            int64_t error_delta) {
  const int64_t effective_error_delta = has_error ? error_delta : reject_delta;
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    for (int i = 0; i < 12; ++i) {
      const int64_t new_reject =
          static_cast<int64_t>(pd.reject_limit[i]) + reject_delta;
      const int64_t new_error =
          static_cast<int64_t>(pd.error_limit[i]) + effective_error_delta;
      pd.reject_limit[i] =
          new_reject < 0 ? 0u : static_cast<uint64_t>(new_reject);
      pd.error_limit[i] = new_error < 0 ? 0u : static_cast<uint64_t>(new_error);
    }
  }
}

void SpecifyManager::SetGlobalPulseLimitPercents(uint8_t reject_pct,
                                                 uint8_t error_pct) {
  reject_pulse_pct_ = reject_pct;
  error_pulse_pct_ = error_pct;
}

void SpecifyManager::AddInterconnectDelay(InterconnectDelay delay) {
  if (delay.src_port.empty()) {
    interconnect_delays_.erase(
        std::remove_if(interconnect_delays_.begin(), interconnect_delays_.end(),
                       [&](const InterconnectDelay& existing) {
                         return existing.dst_port == delay.dst_port;
                       }),
        interconnect_delays_.end());
    interconnect_delays_.push_back(std::move(delay));
    return;
  }

  for (auto& existing : interconnect_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port) {
      existing = std::move(delay);
      return;
    }
  }
  interconnect_delays_.push_back(std::move(delay));
}

uint64_t SpecifyManager::GetPathDelay(std::string_view src,
                                      std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) {
      return pd.delays[0];
    }
  }
  return 0;
}

bool SpecifyManager::HasPathDelay(std::string_view src,
                                  std::string_view dst) const {
  for (const auto& pd : path_delays_) {
    if (pd.src_port == src && pd.dst_port == dst) return true;
  }
  return false;
}

bool SpecifyManager::CheckSetupViolation(std::string_view ref,
                                         uint64_t ref_time,
                                         std::string_view data,
                                         uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSetup) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

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

    if (data_time >= ref_time && data_time - ref_time < check.limit)
      return true;
  }
  return false;
}

// Shared implementation for the two-sided timing checks (recrem / setuphold).
// Both checks share an identical structure: filter by kind/signals, handle the
// negative-timing-check window, then compare the elapsed time against a pair of
// limits. The only behavioral difference is which limit applies on each side of
// the reference time: recrem uses limit2 for the "before" side and limit for
// the "after" side, while setuphold uses the opposite. `lower_side_limit`
// selects which member is compared when data_time <= ref_time, and
// `upper_side_limit` when data_time > ref_time.
static bool CheckTimingViolation(
    const std::vector<TimingCheckEntry>& timing_checks, TimingCheckKind kind,
    std::string_view ref, uint64_t ref_time, std::string_view data,
    uint64_t data_time, uint64_t TimingCheckEntry::* lower_side_limit,
    uint64_t TimingCheckEntry::* upper_side_limit) {
  for (const auto& check : timing_checks) {
    if (check.kind != kind) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;
    if (check.negative_timing_check_enabled) {
      const int64_t ref_t = static_cast<int64_t>(ref_time);
      const int64_t data_t = static_cast<int64_t>(data_time);
      const int64_t lower = ref_t - check.signed_limit;
      const int64_t upper = ref_t + check.signed_limit2;
      if (data_t > lower && data_t < upper) return true;
      continue;
    }

    if (check.limit == 0 && check.limit2 == 0) continue;
    if (data_time <= ref_time) {
      if (ref_time - data_time < check.*lower_side_limit) return true;
    } else {
      if (data_time - ref_time < check.*upper_side_limit) return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kRecrem, ref, ref_time, data, data_time,
      &TimingCheckEntry::limit2, &TimingCheckEntry::limit);
}

bool SpecifyManager::CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                                        std::string_view data,
                                        uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kSkew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

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

    if (data_time <= ref_time) continue;
    uint64_t elapsed = data_time - ref_time;

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

    int64_t begin =
        static_cast<int64_t>(leading_ref_time) - check.start_edge_offset;
    int64_t end =
        static_cast<int64_t>(trailing_ref_time) + check.end_edge_offset;
    int64_t t = static_cast<int64_t>(data_time);

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

    if (data_time <= ref_time) continue;

    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

bool ReportsFullskewViolation(uint64_t timestamp_time, uint64_t next_event_time,
                              bool next_event_is_timecheck, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= timestamp_time) return false;
  uint64_t elapsed = next_event_time - timestamp_time;
  if (event_based_flag) {
    return next_event_is_timecheck && elapsed > limit;
  }

  return elapsed > limit;
}

FullskewWindowAction FullskewSecondTimestampAction(
    bool timestamp_condition_holds, bool remain_active_flag) {
  // A timestamp whose condition holds (or that carries no condition) always
  // opens a fresh timing window, superseding any window in progress and
  // re-arming the check if it was dormant.
  if (timestamp_condition_holds) return FullskewWindowAction::kReplaceWindow;

  // With a false condition the remain_active_flag is decisive: when set, the
  // event is discarded and the existing window stands; when clear, the check
  // turns dormant.
  if (remain_active_flag) return FullskewWindowAction::kIgnore;
  return FullskewWindowAction::kGoDormant;
}

bool ReportsTimeskewViolation(uint64_t ref_time, uint64_t next_event_time,
                              bool next_event_is_data, uint64_t limit,
                              bool event_based_flag) {
  if (next_event_time <= ref_time) return false;
  uint64_t elapsed = next_event_time - ref_time;
  if (event_based_flag) {
    return next_event_is_data && elapsed > limit;
  }

  return elapsed > limit;
}

Logic4Word ToggleNotifierOnViolation(Logic4Word current) {
  const bool pre_a = (current.aval & 1u) != 0u;
  const bool pre_b = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (pre_a && pre_b) {
    result.aval = 1u;
    result.bval = 1u;
  } else if (pre_b) {
    result.aval = 0u;
    result.bval = 0u;
  } else if (pre_a) {
    result.aval = 0u;
    result.bval = 0u;
  } else {
    result.aval = 1u;
    result.bval = 0u;
  }
  return result;
}

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

bool IsSingleSignalTimingCheck(TimingCheckKind kind) {
  return kind == TimingCheckKind::kWidth || kind == TimingCheckKind::kPeriod;
}

uint64_t TimingCheckExpandedCount(TimingCheckKind kind, uint32_t ref_width,
                                  uint32_t data_width,
                                  TimingCheckVectorMode mode) {
  if (mode == TimingCheckVectorMode::kSingle) return 1u;

  if (IsSingleSignalTimingCheck(kind)) {
    return static_cast<uint64_t>(ref_width);
  }
  return static_cast<uint64_t>(ref_width) * static_cast<uint64_t>(data_width);
}

bool TimingCheckUsesDelayedSignals(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
    case TimingCheckKind::kHold:
    case TimingCheckKind::kSetuphold:
    case TimingCheckKind::kRecovery:
    case TimingCheckKind::kRemoval:
    case TimingCheckKind::kRecrem:
    case TimingCheckKind::kWidth:
    case TimingCheckKind::kPeriod:
    case TimingCheckKind::kNochange:
      return true;

    case TimingCheckKind::kSkew:
    case TimingCheckKind::kFullskew:
    case TimingCheckKind::kTimeskew:
      return false;
  }
  return false;
}

AdjustedNegativeTimingLimit AdjustNegativeTimingCheckLimit(
    int64_t adjusted_limit) {
  if (adjusted_limit <= 0) {
    return {0u, true};
  }
  return {static_cast<uint64_t>(adjusted_limit), false};
}

bool NegativeTimingWindowCanYieldViolation(int64_t lower, int64_t upper,
                                           uint64_t precision_ticks) {
  if (upper <= lower) return false;

  const int64_t min_width = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= min_width;
}

bool ZeroSmallestNegativeTimingLimit(std::vector<int64_t>& limits) {
  size_t best_index = limits.size();
  for (size_t i = 0; i < limits.size(); ++i) {
    if (limits[i] >= 0) continue;
    if (best_index == limits.size() || limits[i] > limits[best_index]) {
      best_index = i;
    }
  }
  if (best_index == limits.size()) return false;
  limits[best_index] = 0;
  return true;
}

NegativeTimingConditionRole TimestampConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }

  if (signed_setup < 0) return NegativeTimingConditionRole::kRef;

  if (signed_hold < 0) return NegativeTimingConditionRole::kData;

  return NegativeTimingConditionRole::kBoth;
}

NegativeTimingConditionRole TimecheckConditionRole(int64_t signed_setup,
                                                   int64_t signed_hold) {
  if (signed_setup < 0 && signed_hold < 0) {
    return NegativeTimingConditionRole::kNone;
  }
  if (signed_setup < 0) return NegativeTimingConditionRole::kData;
  if (signed_hold < 0) return NegativeTimingConditionRole::kRef;
  return NegativeTimingConditionRole::kBoth;
}

bool NegativeTimingCheckNotifierShouldToggle(bool delayed_adjusted_violation,
                                             bool) {
  return delayed_adjusted_violation;
}

bool NegativeTimingCheckOptionActive(bool negative_timing_check_option_enabled,
                                     bool all_timing_checks_disabled) {
  return negative_timing_check_option_enabled && !all_timing_checks_disabled;
}

int64_t EffectiveTimingCheckSignalDelay(int64_t requested_delay,
                                        bool negative_timing_option_active) {
  if (!negative_timing_option_active) return 0;
  return requested_delay;
}

bool SpecifyManager::CheckSetupholdViolation(std::string_view ref,
                                             uint64_t ref_time,
                                             std::string_view data,
                                             uint64_t data_time) const {
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kSetuphold, ref, ref_time, data,
      data_time, &TimingCheckEntry::limit, &TimingCheckEntry::limit2);
}

}  // namespace delta
