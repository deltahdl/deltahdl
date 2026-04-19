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
