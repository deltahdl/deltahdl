#include "simulation/sim_context.h"

#include "common/diagnostic.h"
#include "simulation/process.h"

namespace delta {

SimContext::SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag)
    : scheduler_(sched), arena_(arena), diag_(diag) {}

Variable* SimContext::FindVariable(std::string_view name) {
  auto it = variables_.find(name);
  if (it != variables_.end()) return it->second;
  return nullptr;
}

Variable* SimContext::CreateVariable(std::string_view name, uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4Vec(arena_, width);
  // Initialize to X (bval=all-ones) per IEEE 1800-2023 §6.3.
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].bval = ~uint64_t{0};
  }
  variables_[name] = var;
  return var;
}

void SimContext::RegisterFinalProcess(Process* proc) {
  final_processes_.push_back(proc);
}

void SimContext::RunFinalBlocks() {
  for (auto* proc : final_processes_) {
    proc->Resume();
  }
}

}  // namespace delta
