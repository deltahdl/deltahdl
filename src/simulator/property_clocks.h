#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_stmt.h"

namespace delta {

class SimContext;

struct PropertyClocks {
  std::vector<std::vector<EventExpr>> clocks;
  std::vector<std::vector<SimTime>> ticks;
  std::vector<bool> was_true;
  bool multiclock = false;
  SimTime installed_at;
  static constexpr SimTime kNever{~static_cast<uint64_t>(0)};
};

int ClockIndexOf(PropertyClocks& clocks, const std::vector<EventExpr>& clock);

void InstallClockWatchers(PropertyClocks& clocks, SimContext& ctx,
                          Arena& arena);

uint32_t ClocksTicked(const PropertyClocks& clocks, SimTime now);

void ForgetTicksBefore(PropertyClocks& clocks, SimTime now);

bool WokenByAnotherClock(const PropertyClocks& clocks, const EventExpr& woke);

}  // namespace delta
