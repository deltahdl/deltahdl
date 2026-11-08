#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

enum class PulseLimitSource : uint8_t {
  kDefault = 0,
  kGlobal = 1,
  kPathpulse = 2,
  kSdf = 3,
};

struct PathDelay {
  std::string src_port;
  std::string dst_port;
  std::string src_select;
  std::string dst_select;
  std::string decl_src_port;
  std::string decl_dst_port;
  std::string inst_prefix;
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;

  std::string condition;

  const Expr* condition_expr = nullptr;

  bool is_ifnone = false;
  uint8_t delay_count = 1;
  uint64_t delays[12] = {};
  std::vector<const Expr*> source_delays;
  SourceLoc loc;
  const SpecifyPathDecl* decl = nullptr;
  std::size_t src_index = 0;
  std::size_t dst_index = 0;

  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
  PulseLimitSource reject_limit_source = PulseLimitSource::kDefault;
  PulseLimitSource error_limit_source = PulseLimitSource::kDefault;
};

uint64_t ClampPathDelay(int64_t signed_value);

void ExpandTransitionDelays(PathDelay& pd);

class SimContext;
class Scheduler;

PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena, std::size_t src_index = 0,
                                 std::size_t dst_index = 0);

std::vector<std::string> CollectDeclaredSpecparams(const ModuleDecl& mod);

bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams);

struct PrimitiveDriver {
  std::string output_port;
  std::string inst_prefix;
  uint8_t delay_count = 1;
  uint64_t delays[12] = {};
  bool sdf_annotated = false;
  bool drives_module_output = true;
};

std::vector<PrimitiveDriver> BuildPrimitiveDriversFromGate(
    const ModuleItem& gate, SimContext& ctx, Arena& arena);

struct PathCandidate {
  const PathDelay* path = nullptr;
  uint64_t last_transition_time = 0;
  bool condition_true = true;
};

const PathDelay* SelectActivePath(const std::vector<PathCandidate>& candidates,
                                  uint8_t transition_slot);

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot);

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

enum class PulseStyle : uint8_t {
  kOnEvent,
  kOnDetect,
};

uint64_t FilteredPulseLeadingXTime(PulseStyle style, uint64_t detect_time,
                                   uint64_t scheduled_leading_time);

enum class ShowCancelled : uint8_t {
  kNoshowcancelled,
  kShowcancelled,
};

bool IsNegativePulse(uint64_t leading_time, uint64_t trailing_time);

struct NegativePulseSchedule {
  bool force_x;
  uint64_t x_time;
};

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

inline uint64_t EffectivePulseLimit(uint64_t limit, uint64_t delay) {
  return limit < delay ? limit : delay;
}

}  // namespace delta
