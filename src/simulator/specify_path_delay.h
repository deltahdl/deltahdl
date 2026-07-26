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
class Scheduler;

// §30.5.1: turn a parsed module path assignment into the runtime PathDelay that
// carries its transition delays. Each listed delay expression is evaluated in
// `ctx`; a single value is the typical delay and a min:typ:max triple selects a
// member per the context's delay mode. A delay that evaluates to a negative
// value is treated as zero, and the resulting one/two/three/six/twelve values
// are distributed across all twelve transition slots per Table 30-2.
PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena);

// §32.4.3: the names a module introduced as specparams. These are the only
// names an SDF LABEL section has anything to annotate, so collecting them is
// the first half of applying a LABEL. Both declaration sites count: a specparam
// declared among the module items and one declared inside a specify block.
std::vector<std::string> CollectDeclaredSpecparams(const ModuleDecl& mod);

// §32.4.3: does this expression read one or more of `specparams`? A LABEL
// annotation has to reevaluate every expression containing a specparam, and
// leave every other expression alone, so this predicate is what separates the
// two. The whole expression tree is walked, so a specparam reached only through
// nested operands still counts.
bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams);

// §32.4.1 Table 32-1: one module output driven by a gate primitive, together
// with the propagation delays that primitive was declared with. A DEVICE delay
// falls back to these when the module declares no specify path for the output
// the entry names.
struct PrimitiveDriver {
  std::string output_port;
  uint8_t delay_count = 1;
  uint64_t delays[12] = {};
};

// §32.4.1: collect the module-output drivers one gate instantiation
// contributes. A gate that drives nothing (the bidirectional pass-gate family)
// yields no drivers, while the buffer/inverter family yields one per output
// terminal. The gate's declared delay expressions are evaluated in `ctx` and
// spread over the twelve transition slots the same way a module path delay is.
std::vector<PrimitiveDriver> BuildPrimitiveDriversFromGate(
    const ModuleItem& gate, SimContext& ctx, Arena& arena);

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

}  // namespace delta
