#include "simulation/clocking.h"

#include <string_view>
#include <utility>

#include "common/types.h"

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

const ClockingSignal* ClockingManager::FindSignal(
    const ClockingBlock& block, std::string_view signal_name) const {
  for (const auto& sig : block.signals) {
    if (sig.signal_name == signal_name) return &sig;
  }
  return nullptr;
}

}  // namespace delta
