#pragma once

#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

namespace delta {

class DiagEngine;
struct Process;

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag);

  Variable* FindVariable(std::string_view name);
  Variable* CreateVariable(std::string_view name, uint32_t width);

  Scheduler& GetScheduler() { return scheduler_; }
  Arena& GetArena() { return arena_; }
  DiagEngine& GetDiag() { return diag_; }
  SimTime CurrentTime() const { return scheduler_.CurrentTime(); }

  void RequestStop() { stop_requested_ = true; }
  bool StopRequested() const { return stop_requested_; }

  void RegisterFinalProcess(Process* proc);
  void RunFinalBlocks();

 private:
  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::vector<Process*> final_processes_;
  bool stop_requested_ = false;
};

}  // namespace delta
