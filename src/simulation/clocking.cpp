#include "simulation/clocking.h"

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

namespace delta {

// =============================================================================
// ClockingManager
// =============================================================================

void ClockingManager::Register(ClockingBlock block) {
  name_index_[block.name] = blocks_.size();
  blocks_.push_back(std::move(block));
}

const ClockingBlock* ClockingManager::Find(std::string_view name) const {
  auto it = name_index_.find(name);
  if (it == name_index_.end()) return nullptr;
  return &blocks_[it->second];
}

SimTime ClockingManager::GetInputSkew(std::string_view block_name,
                                      std::string_view signal_name) const {
  const auto* block = Find(block_name);
  if (block == nullptr) return SimTime{0};
  const auto* sig = FindSignal(*block, signal_name);
  if (sig != nullptr && sig->skew.ticks != 0) return sig->skew;
  return block->default_input_skew;
}

SimTime ClockingManager::GetOutputSkew(std::string_view block_name,
                                       std::string_view signal_name) const {
  const auto* block = Find(block_name);
  if (block == nullptr) return SimTime{0};
  const auto* sig = FindSignal(*block, signal_name);
  if (sig != nullptr && sig->skew.ticks != 0) return sig->skew;
  return block->default_output_skew;
}

// Check if the clock variable transitioned to the expected edge.
static bool CheckClockEdge(Variable* clk_var, Edge edge) {
  uint64_t cur = clk_var->value.ToUint64() & 1;
  uint64_t prev = clk_var->prev_value.ToUint64() & 1;
  if (edge == Edge::kPosedge) return prev == 0 && cur == 1;
  if (edge == Edge::kNegedge) return prev == 1 && cur == 0;
  return prev != cur;  // Edge::kNone means any change.
}

// Sample all input signals for a clocking block.
static void SampleBlockInputs(ClockingManager* mgr, const std::string& name,
                              const std::vector<ClockingSignal>& signals,
                              SimContext& ctx) {
  for (const auto& sig : signals) {
    bool is_input = (sig.direction == ClockingDir::kInput ||
                     sig.direction == ClockingDir::kInout);
    if (!is_input) continue;
    auto* var = ctx.FindVariable(sig.signal_name);
    if (!var) continue;
    mgr->SampleInput(name, sig.signal_name, var->value.ToUint64());
  }
}

// Re-registrable clock watcher that samples inputs on the correct edge.
static void RegisterClockWatcher(ClockingManager* mgr, Variable* clk_var,
                                 const ClockingBlock& block, SimContext& ctx,
                                 Scheduler& sched) {
  auto block_name = std::string(block.name);
  auto signals = block.signals;
  auto edge = block.clock_edge;
  clk_var->AddWatcher(
      [mgr, clk_var, block_name, signals, edge, &ctx, &sched]() {
        if (!CheckClockEdge(clk_var, edge)) {
          auto* blk = mgr->Find(block_name);
          if (blk) RegisterClockWatcher(mgr, clk_var, *blk, ctx, sched);
          return true;
        }
        SampleBlockInputs(mgr, block_name, signals, ctx);
        mgr->NotifyBlockEvent(block_name);
        mgr->InvokeEdgeCallbacks(block_name);
        auto* blk = mgr->Find(block_name);
        if (blk) RegisterClockWatcher(mgr, clk_var, *blk, ctx, sched);
        return true;
      });
}

void ClockingManager::Attach(SimContext& ctx, Scheduler& sched) {
  for (const auto& block : blocks_) {
    auto* clk_var = ctx.FindVariable(block.clock_signal);
    if (!clk_var) continue;
    RegisterClockWatcher(this, clk_var, block, ctx, sched);
  }
}

void ClockingManager::SampleInput(std::string_view block_name,
                                  std::string_view signal_name,
                                  uint64_t value) {
  sampled_values_[{std::string(block_name), std::string(signal_name)}] = value;
}

uint64_t ClockingManager::GetSampledValue(std::string_view block_name,
                                          std::string_view signal_name) const {
  auto it =
      sampled_values_.find({std::string(block_name), std::string(signal_name)});
  if (it != sampled_values_.end()) return it->second;
  return 0;
}

void ClockingManager::ScheduleOutputDrive(std::string_view block_name,
                                          std::string_view signal_name,
                                          uint64_t value, SimContext& ctx,
                                          Scheduler& sched) {
  auto skew = GetOutputSkew(block_name, signal_name);
  auto drive_time = sched.CurrentTime() + skew;
  auto sig_name = std::string(signal_name);
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&ctx, sig_name, value]() {
    auto* var = ctx.FindVariable(sig_name);
    if (!var) return;
    var->value.words[0].aval = value;
    var->value.words[0].bval = 0;
  };
  sched.ScheduleEvent(drive_time, Region::kNBA, ev);
}

// S14.8: Associate an event variable with a clocking block.
void ClockingManager::SetBlockEventVar(std::string_view block_name,
                                       Variable* var) {
  block_event_vars_[block_name] = var;
}

void ClockingManager::NotifyBlockEvent(std::string_view block_name) {
  auto it = block_event_vars_.find(block_name);
  if (it != block_event_vars_.end() && it->second) {
    it->second->NotifyWatchers();
  }
}

// Register an edge callback for a clocking block.
void ClockingManager::RegisterEdgeCallback(std::string_view block_name,
                                           SimContext& /*ctx*/,
                                           Scheduler& /*sched*/,
                                           std::function<void()> cb) {
  auto bn = std::string(block_name);
  edge_callbacks_[bn].push_back(std::move(cb));

  // If the block is already attached, ensure watchers are re-established.
  // The next edge detection will invoke callbacks.
}

void ClockingManager::InvokeEdgeCallbacks(std::string_view block_name) {
  auto it = edge_callbacks_.find(std::string(block_name));
  if (it == edge_callbacks_.end()) return;
  for (auto& cb : it->second) {
    cb();
  }
}

const ClockingSignal* ClockingManager::FindSignal(
    const ClockingBlock& block, std::string_view signal_name) const {
  for (const auto& sig : block.signals) {
    if (sig.signal_name == signal_name) return &sig;
  }
  return nullptr;
}

}  // namespace delta
