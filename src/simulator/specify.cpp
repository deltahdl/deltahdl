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
      const uint64_t kT = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = kT;
      break;
    }
    case 2: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      pd.delays[2] = kTrise;
      pd.delays[3] = kTrise;
      pd.delays[4] = kTfall;
      pd.delays[5] = kTfall;
      break;
    }
    case 3: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      const uint64_t kTz = pd.delays[2];
      pd.delays[3] = kTrise;
      pd.delays[4] = kTz;
      pd.delays[5] = kTfall;
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
  const bool kUnknown = (condition_lsb.bval & 1u) != 0u;
  if (kUnknown) return true;
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
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
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
  const uint64_t kEffectiveError = has_error ? error : reject;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = reject;
    pd.error_limit[i] = kEffectiveError;
  }
}

namespace {

// Overwrites `existing` with `replacement` while optionally retaining the
// original pulse (reject/error) limits.
void ReplacePathDelayPreservingPulse(PathDelay& existing, PathDelay replacement,
                                     bool preserve_pulse_limits) {
  uint64_t saved_reject[12];
  uint64_t saved_error[12];
  if (preserve_pulse_limits) {
    for (int i = 0; i < 12; ++i) {
      saved_reject[i] = existing.reject_limit[i];
      saved_error[i] = existing.error_limit[i];
    }
  }
  existing = std::move(replacement);
  if (preserve_pulse_limits) {
    for (int i = 0; i < 12; ++i) {
      existing.reject_limit[i] = saved_reject[i];
      existing.error_limit[i] = saved_error[i];
    }
  }
}

// Nonconditional SDF update: overwrites every existing path delay between the
// same ports, but keeps each entry's original condition/ifnone (and optionally
// its pulse limits). Returns true if at least one entry matched.
bool UpdateNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delay,
                                    bool preserve_pulse_limits) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port) {
      std::string saved_cond = existing.condition;
      bool saved_ifnone = existing.is_ifnone;
      ReplacePathDelayPreservingPulse(existing, delay, preserve_pulse_limits);
      existing.condition = std::move(saved_cond);
      existing.is_ifnone = saved_ifnone;
      matched = true;
    }
  }
  return matched;
}

}  // namespace

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    if (!UpdateNonconditionalPathDelays(path_delays_, delay,
                                        preserve_pulse_limits)) {
      path_delays_.push_back(std::move(delay));
    }
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.condition == delay.condition &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayPreservingPulse(existing, std::move(delay),
                                      preserve_pulse_limits);
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

namespace {

void AddPathDelayValues(PathDelay& existing, const PathDelay& delta) {
  for (int i = 0; i < 12; ++i) existing.delays[i] += delta.delays[i];
}

// Adds `delta` to every existing path delay between the same ports (ignoring
// condition/ifnone). Returns true if at least one entry matched.
bool IncrementNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                       const PathDelay& delta) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      AddPathDelayValues(existing, delta);
      matched = true;
    }
  }
  return matched;
}

// Adds `delta` to the first existing path delay matching ports plus
// condition/ifnone. Returns true if a matching entry was found.
bool IncrementConditionalPathDelay(std::vector<PathDelay>& path_delays,
                                   const PathDelay& delta) {
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        existing.condition == delta.condition &&
        existing.is_ifnone == delta.is_ifnone) {
      AddPathDelayValues(existing, delta);
      return true;
    }
  }
  return false;
}

}  // namespace

void SpecifyManager::IncrementPathDelay(const PathDelay& delta) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  const bool kMatched =
      kSdfIsNonconditional
          ? IncrementNonconditionalPathDelays(path_delays_, delta)
          : IncrementConditionalPathDelay(path_delays_, delta);
  if (!kMatched) path_delays_.push_back(delta);
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

namespace {

bool SdfAnnotationMatchesCheck(const TimingCheckEntry& existing,
                               const SdfTcAnnotation& a) {
  if (existing.kind != a.kind) return false;
  if (existing.ref_signal != a.ref_signal) return false;
  if (existing.data_signal != a.data_signal) return false;
  if (a.ref_edge != SpecifyEdge::kNone && existing.ref_edge != a.ref_edge)
    return false;
  if (a.data_edge != SpecifyEdge::kNone && existing.data_edge != a.data_edge)
    return false;
  if (!a.condition.empty() && existing.condition != a.condition) return false;
  return true;
}

void ApplySdfAnnotationFields(TimingCheckEntry& check,
                              const SdfTcAnnotation& a) {
  if (a.set_limit) check.limit = a.limit;
  if (a.set_limit2) check.limit2 = a.limit2;
  if (a.set_start_edge_offset) check.start_edge_offset = a.start_edge_offset;
  if (a.set_end_edge_offset) check.end_edge_offset = a.end_edge_offset;
}

TimingCheckEntry BuildTimingCheckFromAnnotation(const SdfTcAnnotation& a) {
  TimingCheckEntry e;
  e.kind = a.kind;
  e.ref_signal = a.ref_signal;
  e.ref_edge = a.ref_edge;
  e.data_signal = a.data_signal;
  e.data_edge = a.data_edge;
  e.condition = a.condition;
  ApplySdfAnnotationFields(e, a);
  return e;
}

}  // namespace

void SpecifyManager::AnnotateSdfTimingCheck(const SdfTcAnnotation& a) {
  bool matched = false;
  for (auto& existing : timing_checks_) {
    if (!SdfAnnotationMatchesCheck(existing, a)) continue;
    ApplySdfAnnotationFields(existing, a);
    matched = true;
  }
  if (matched) return;

  timing_checks_.push_back(BuildTimingCheckFromAnnotation(a));
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
  std::string name = std::move(delta.name);
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

namespace {

void ApplySdfPercentPulseLimits(PathDelay& pd, uint64_t reject, bool has_error,
                                uint64_t error) {
  uint64_t reject_pct = reject;
  uint64_t error_pct = has_error ? error : reject;
  if (error_pct < reject_pct) error_pct = reject_pct;
  for (int i = 0; i < 12; ++i) {
    pd.reject_limit[i] = pd.delays[i] * reject_pct / 100;
    pd.error_limit[i] = pd.delays[i] * error_pct / 100;
  }
}

void ClampPulseLimitsToDelays(PathDelay& pd) {
  for (int i = 0; i < 12; ++i) {
    if (pd.reject_limit[i] > pd.delays[i]) pd.reject_limit[i] = pd.delays[i];
    if (pd.error_limit[i] > pd.delays[i]) pd.error_limit[i] = pd.delays[i];
  }
}

}  // namespace

void SpecifyManager::AddSdfPulseLimit(const SdfPulseLimitSpec& spec) {
  for (auto& pd : path_delays_) {
    if (pd.src_port != spec.src || pd.dst_port != spec.dst) continue;
    if (spec.is_percent) {
      ApplySdfPercentPulseLimits(pd, spec.reject, spec.has_error, spec.error);
    } else {
      ApplySdfPulseLimits(pd, spec.reject, spec.has_error, spec.error);
    }
    ClampPulseLimitsToDelays(pd);
  }
}

void SpecifyManager::IncrementSdfPulseLimit(std::string_view src,
                                            std::string_view dst,
                                            int64_t reject_delta,
                                            bool has_error,
                                            int64_t error_delta) {
  const int64_t kEffectiveErrorDelta = has_error ? error_delta : reject_delta;
  for (auto& pd : path_delays_) {
    if (pd.src_port != src || pd.dst_port != dst) continue;
    for (int i = 0; i < 12; ++i) {
      const int64_t kNewReject =
          static_cast<int64_t>(pd.reject_limit[i]) + reject_delta;
      const int64_t kNewError =
          static_cast<int64_t>(pd.error_limit[i]) + kEffectiveErrorDelta;
      pd.reject_limit[i] =
          kNewReject < 0 ? 0u : static_cast<uint64_t>(kNewReject);
      pd.error_limit[i] = kNewError < 0 ? 0u : static_cast<uint64_t>(kNewError);
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
namespace {

// A single observed reference/data transition pair to test against the timing
// checks (IEEE 1800 §31): the reference event (signal + time) and the data
// event (signal + time) that together describe one timing-check observation.
struct TimingCheckEvent {
  std::string_view ref;
  uint64_t ref_time;
  std::string_view data;
  uint64_t data_time;
};

// Selects which TimingCheckEntry limit applies on each side of the reference
// time for two-sided checks (recrem / setuphold): `lower` is compared when the
// data event is on/before the reference, `upper` when it is after.
struct TwoSidedLimitSelector {
  uint64_t TimingCheckEntry::* lower;
  uint64_t TimingCheckEntry::* upper;
};

// True when `data_time` falls inside the negative-timing-check window centered
// on `ref_time` and spanning [-signed_limit, +signed_limit2].
bool NegativeTimingWindowViolated(const TimingCheckEntry& check,
                                  uint64_t ref_time, uint64_t data_time) {
  const auto kRefT = static_cast<int64_t>(ref_time);
  const auto kDataT = static_cast<int64_t>(data_time);
  const int64_t kLower = kRefT - check.signed_limit;
  const int64_t kUpper = kRefT + check.signed_limit2;
  return kDataT > kLower && kDataT < kUpper;
}

// True when the elapsed time between `ref_time` and `data_time` violates the
// side-specific limit (lower side for data on/before ref, upper side after).
bool TwoSidedLimitViolated(const TimingCheckEntry& check, uint64_t ref_time,
                           uint64_t data_time,
                           uint64_t TimingCheckEntry::* lower_side_limit,
                           uint64_t TimingCheckEntry::* upper_side_limit) {
  if (check.limit == 0 && check.limit2 == 0) return false;
  if (data_time <= ref_time) {
    return ref_time - data_time < check.*lower_side_limit;
  }
  return data_time - ref_time < check.*upper_side_limit;
}

}  // namespace

static bool CheckTimingViolation(
    const std::vector<TimingCheckEntry>& timing_checks, TimingCheckKind kind,
    const TimingCheckEvent& event, const TwoSidedLimitSelector& selector) {
  for (const auto& check : timing_checks) {
    if (check.kind != kind) continue;
    if (check.ref_signal != event.ref) continue;
    if (check.data_signal != event.data) continue;
    if (check.negative_timing_check_enabled) {
      if (NegativeTimingWindowViolated(check, event.ref_time, event.data_time))
        return true;
      continue;
    }
    if (TwoSidedLimitViolated(check, event.ref_time, event.data_time,
                              selector.lower, selector.upper)) {
      return true;
    }
  }
  return false;
}

bool SpecifyManager::CheckRecremViolation(std::string_view ref,
                                          uint64_t ref_time,
                                          std::string_view data,
                                          uint64_t data_time) const {
  return CheckTimingViolation(
      timing_checks_, TimingCheckKind::kRecrem,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit2, &TimingCheckEntry::limit});
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

namespace {

bool FullskewWindowViolated(const TimingCheckEntry& check, uint64_t ref_time,
                            uint64_t data_time) {
  if (ref_time < data_time) {
    return data_time - ref_time > check.limit;
  }
  if (data_time < ref_time) {
    return ref_time - data_time > check.limit2;
  }
  return false;
}

}  // namespace

bool SpecifyManager::CheckFullskewViolation(std::string_view ref,
                                            uint64_t ref_time,
                                            std::string_view data,
                                            uint64_t data_time) const {
  for (const auto& check : timing_checks_) {
    if (check.kind != TimingCheckKind::kFullskew) continue;
    if (check.ref_signal != ref) continue;
    if (check.data_signal != data) continue;

    if (FullskewWindowViolated(check, ref_time, data_time)) return true;
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
    auto t = static_cast<int64_t>(data_time);

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
  const bool kPreA = (current.aval & 1u) != 0u;
  const bool kPreB = (current.bval & 1u) != 0u;
  Logic4Word result;
  if (kPreA && kPreB) {
    result.aval = 1u;
    result.bval = 1u;
  } else if (kPreB || kPreA) {
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
  const bool kNown = (conditioning_lsb.bval & 1u) == 0u;
  if (!kNown) {
    return !IsDeterministicTimingCheckCondition(kind);
  }
  const auto kBit = static_cast<uint8_t>(conditioning_lsb.aval & 1u);
  const auto kRhs = static_cast<uint8_t>(scalar_constant_bit & 1u);
  switch (kind) {
    case TimingCheckConditionKind::kPlain:
      return kBit == 1u;
    case TimingCheckConditionKind::kNegate:
      return kBit == 0u;
    case TimingCheckConditionKind::kEq:
    case TimingCheckConditionKind::kCaseEq:
      return kBit == kRhs;
    case TimingCheckConditionKind::kNeq:
    case TimingCheckConditionKind::kCaseNeq:
      return kBit != kRhs;
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

  const int64_t kMinWidth = 2 * static_cast<int64_t>(precision_ticks);
  return (upper - lower) >= kMinWidth;
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
      timing_checks_, TimingCheckKind::kSetuphold,
      {ref, ref_time, data, data_time},
      {&TimingCheckEntry::limit, &TimingCheckEntry::limit2});
}

}  // namespace delta
