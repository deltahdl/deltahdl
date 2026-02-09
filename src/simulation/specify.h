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
  uint64_t rise_delay = 0;
  uint64_t fall_delay = 0;
  uint64_t z_delay = 0;  // Transition to Z (tri-state)
};

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
  std::string notifier;
};

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
