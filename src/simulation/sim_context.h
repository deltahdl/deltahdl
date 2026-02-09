#pragma once

#include <cstdint>
#include <random>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

namespace delta {

class DiagEngine;
class DpiContext;
class VcdWriter;
struct ModuleItem;
struct Process;

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0);

  Variable* FindVariable(std::string_view name);
  Variable* CreateVariable(std::string_view name, uint32_t width);

  Net* FindNet(std::string_view name);
  Net* CreateNet(std::string_view name, NetType type, uint32_t width);

  Scheduler& GetScheduler() { return scheduler_; }
  Arena& GetArena() { return arena_; }
  DiagEngine& GetDiag() { return diag_; }
  SimTime CurrentTime() const { return scheduler_.CurrentTime(); }

  void RequestStop() { stop_requested_ = true; }
  bool StopRequested() const { return stop_requested_; }

  void RegisterFinalProcess(Process* proc);
  void RunFinalBlocks();

  void AddSensitivity(std::string_view signal, Process* proc);
  const std::vector<Process*>& GetSensitiveProcesses(
      std::string_view signal) const;

  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void PushScope();
  void PopScope();
  Variable* FindLocalVariable(std::string_view name);
  Variable* CreateLocalVariable(std::string_view name, uint32_t width);

  void SetVcdWriter(VcdWriter* vcd) { vcd_writer_ = vcd; }
  VcdWriter* GetVcdWriter() { return vcd_writer_; }

  void SetDpiContext(DpiContext* dpi) { dpi_context_ = dpi; }
  DpiContext* GetDpiContext() { return dpi_context_; }

  const std::unordered_map<std::string_view, Variable*>& GetVariables() const {
    return variables_;
  }

  int32_t Random32();
  uint32_t Urandom32();
  uint32_t UrandomRange(uint32_t min_val, uint32_t max_val);

 private:
  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  std::mt19937 rng_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::unordered_map<std::string_view, Net*> nets_;
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::vector<std::unordered_map<std::string_view, Variable*>> scope_stack_;
  std::vector<Process*> final_processes_;
  std::unordered_map<std::string_view, std::vector<Process*>> sensitivity_map_;
  static const std::vector<Process*> kEmptyProcessList;
  VcdWriter* vcd_writer_ = nullptr;
  DpiContext* dpi_context_ = nullptr;
  bool stop_requested_ = false;
};

}  // namespace delta
