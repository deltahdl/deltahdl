#include "simulation/specify.h"

#include <string>
#include <string_view>
#include <utility>

namespace delta {

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
