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

}  // namespace delta
