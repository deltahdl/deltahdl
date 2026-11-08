#pragma once

#include <cstdint>
#include <optional>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct RtlirContAssign;
struct RtlirNet;

struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

std::optional<ContAssignDelays> NetDelayTicks(const RtlirNet& net,
                                              const TimeScale& scale,
                                              SimContext& ctx, Arena& arena);

uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                               const Logic4Vec& new_val,
                               const ContAssignDelays& d, uint32_t width);

struct ContAssignWhole {
  const Expr* lhs = nullptr;
  const Expr* rhs = nullptr;
};

ContAssignWhole WholeOfConcatElement(const RtlirContAssign& ca);

struct ContAssignTransition {
  Logic4Vec old_val;
  Logic4Vec new_val;
  uint32_t width = 0;
};

uint64_t SelectTransitionDelay(const ContAssignWhole& whole,
                               const ContAssignTransition& own,
                               const ContAssignDelays& d, SimContext& ctx,
                               Arena& arena);

}  // namespace delta
