#include "simulator/specify.h"

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
  // Non-x transition slots per Table 30-2:
  //   [0]=0->1, [1]=1->0, [2]=0->z, [3]=z->1, [4]=1->z, [5]=z->0.
  switch (pd.delay_count) {
    case 1: {
      // Count 1: every basic transition uses the single value.
      const uint64_t t = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = t;
      return;
    }
    case 2: {
      // Count 2: trise covers 0->1/0->z/z->1; tfall covers 1->0/1->z/z->0.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      pd.delays[2] = trise;
      pd.delays[3] = trise;
      pd.delays[4] = tfall;
      pd.delays[5] = tfall;
      return;
    }
    case 3: {
      // Count 3: z-bound transitions share tz; trise/tfall keep their slots.
      const uint64_t trise = pd.delays[0];
      const uint64_t tfall = pd.delays[1];
      const uint64_t tz = pd.delays[2];
      pd.delays[3] = trise;
      pd.delays[4] = tz;
      pd.delays[5] = tfall;
      return;
    }
    default:
      // Counts 6 and 12 arrive already laid out as Table 30-2 expects.
      return;
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
    // Setup: data must be stable `limit` time units before ref edge.
    if (ref_time - data_time < check.limit) return true;
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
    // Hold: data must remain stable `limit` time units after ref edge.
    if (data_time - ref_time < check.limit) return true;
  }
  return false;
}

}  // namespace delta
