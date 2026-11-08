#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/exec_task.h"

namespace delta {

class Arena;
class SimContext;
class SpecifyManager;
struct Expr;

uint8_t ModulePathTransitionSlot(const Logic4Vec& from, const Logic4Vec& to);

struct ModulePathDelay {
  bool found = false;
  uint64_t delay = 0;
  uint64_t reject_limit = 0;
  uint64_t error_limit = 0;
  uint64_t source_ticks = 0;
};

bool IsModulePathOutput(const SpecifyManager& mgr, std::string_view output);

struct ModulePathDrive {
  SimContext& ctx;
  Arena& arena;
  const SpecifyManager& mgr;
  std::string_view output;
  const std::vector<std::string_view>& sources;
  const Expr* rhs;
  uint32_t width;
  uint64_t distributed_ticks;
  std::function<void(const Logic4Vec&)> commit;
  bool at_port = false;
};

ModulePathDelay SelectModulePathDelay(const ModulePathDrive& drive,
                                      const Logic4Vec& from,
                                      const Logic4Vec& to);

void WatchModulePathSources(const SpecifyManager& mgr, SimContext& ctx);

std::vector<std::string> ModulePathSourcesOf(const SpecifyManager& mgr,
                                             std::string_view output);

ExecTask RunModulePathTransition(const ModulePathDrive& drive,
                                 const Logic4Vec& old_val, Logic4Vec& val,
                                 bool* committed);

}  // namespace delta
