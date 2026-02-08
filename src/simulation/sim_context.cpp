#include "simulation/sim_context.h"

#include "common/diagnostic.h"
#include "simulation/process.h"

namespace delta {

SimContext::SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
                       uint32_t seed)
    : scheduler_(sched), arena_(arena), diag_(diag), rng_(seed) {}

Variable* SimContext::FindVariable(std::string_view name) {
  auto* local = FindLocalVariable(name);
  if (local) return local;
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

void SimContext::RegisterFunction(std::string_view name, ModuleItem* item) {
  functions_[name] = item;
}

ModuleItem* SimContext::FindFunction(std::string_view name) {
  auto it = functions_.find(name);
  return (it != functions_.end()) ? it->second : nullptr;
}

void SimContext::PushScope() { scope_stack_.emplace_back(); }

void SimContext::PopScope() {
  if (!scope_stack_.empty()) scope_stack_.pop_back();
}

Variable* SimContext::FindLocalVariable(std::string_view name) {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); ++it) {
    auto found = it->find(name);
    if (found != it->end()) return found->second;
  }
  return nullptr;
}

Variable* SimContext::CreateLocalVariable(std::string_view name,
                                          uint32_t width) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4VecVal(arena_, width, 0);
  if (!scope_stack_.empty()) {
    scope_stack_.back()[name] = var;
  }
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

int32_t SimContext::Random32() { return static_cast<int32_t>(rng_()); }

uint32_t SimContext::Urandom32() { return static_cast<uint32_t>(rng_()); }

uint32_t SimContext::UrandomRange(uint32_t min_val, uint32_t max_val) {
  if (min_val > max_val) std::swap(min_val, max_val);
  std::uniform_int_distribution<uint32_t> dist(min_val, max_val);
  return dist(rng_);
}

}  // namespace delta
