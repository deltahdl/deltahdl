#pragma once

#include <cstdint>
#include <random>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

namespace delta {

class DiagEngine;
struct ModuleItem;
struct Process;

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0);

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

  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void PushScope();
  void PopScope();
  Variable* FindLocalVariable(std::string_view name);
  Variable* CreateLocalVariable(std::string_view name, uint32_t width);

  int32_t Random32();
  uint32_t Urandom32();
  uint32_t UrandomRange(uint32_t min_val, uint32_t max_val);

 private:
  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  std::mt19937 rng_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::vector<std::unordered_map<std::string_view, Variable*>> scope_stack_;
  std::vector<Process*> final_processes_;
  bool stop_requested_ = false;
};

}  // namespace delta
