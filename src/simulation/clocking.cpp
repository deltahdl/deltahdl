#include "simulation/clocking.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

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

static void RegisterClockWatcher(ClockingManager* mgr, Variable* clk_var,
                                 const ClockingBlock& block, SimContext& ctx,
                                 Scheduler& sched) {
  auto block_name = std::string(block.name);
  auto signals = block.signals;
  clk_var->AddWatcher([mgr, clk_var, block_name, signals, &ctx, &sched]() {
    // Posedge: prev was 0, current is 1.
    uint64_t cur = clk_var->value.ToUint64() & 1;
    uint64_t prev = clk_var->prev_value.ToUint64() & 1;
    if (prev == 0 && cur == 1) {
      for (const auto& sig : signals) {
        if (sig.direction != ClockingDir::kInput) continue;
        auto* var = ctx.FindVariable(sig.signal_name);
        if (!var) continue;
        mgr->SampleInput(block_name, sig.signal_name, var->value.ToUint64());
      }
    }
    RegisterClockWatcher(mgr, clk_var, *mgr->Find(block_name), ctx, sched);
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

const ClockingSignal* ClockingManager::FindSignal(
    const ClockingBlock& block, std::string_view signal_name) const {
  for (const auto& sig : block.signals) {
    if (sig.signal_name == signal_name) return &sig;
  }
  return nullptr;
}

}  // namespace delta
