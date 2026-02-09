#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

class Scheduler;
class SimContext;

// =============================================================================
// Clocking signal direction
// =============================================================================

enum class ClockingDir : uint8_t {
  kInput,
  kOutput,
  kInout,
};

// =============================================================================
// ClockingSignal: a signal within a clocking block with optional skew
// =============================================================================

struct ClockingSignal {
  std::string_view signal_name;
  ClockingDir direction = ClockingDir::kInput;
  SimTime skew{0};
};

// =============================================================================
// ClockingBlock: a named clocking block with default skews
// =============================================================================

struct ClockingBlock {
  std::string_view name;
  std::string_view clock_signal;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
};

// =============================================================================
// ClockingManager: registers clocking blocks and applies skew
// =============================================================================

class ClockingManager {
 public:
  void Register(ClockingBlock block);
  void Attach(SimContext& ctx, Scheduler& sched);
  const ClockingBlock* Find(std::string_view name) const;
  SimTime GetInputSkew(std::string_view block_name,
                       std::string_view signal_name) const;
  SimTime GetOutputSkew(std::string_view block_name,
                        std::string_view signal_name) const;
  uint64_t GetSampledValue(std::string_view block_name,
                           std::string_view signal_name) const;
  void ScheduleOutputDrive(std::string_view block_name,
                           std::string_view signal_name, uint64_t value,
                           SimContext& ctx, Scheduler& sched);
  void SampleInput(std::string_view block_name, std::string_view signal_name,
                   uint64_t value);
  uint32_t Count() const { return static_cast<uint32_t>(blocks_.size()); }

 private:
  using SampleKey = std::pair<std::string, std::string>;
  struct PairHash {
    size_t operator()(const SampleKey& p) const {
      auto h1 = std::hash<std::string>{}(p.first);
      auto h2 = std::hash<std::string>{}(p.second);
      return h1 ^ (h2 << 1);
    }
  };

  const ClockingSignal* FindSignal(const ClockingBlock& block,
                                   std::string_view signal_name) const;

  std::vector<ClockingBlock> blocks_;
  std::unordered_map<std::string_view, size_t> name_index_;
  std::unordered_map<SampleKey, uint64_t, PairHash> sampled_values_;
};

}  // namespace delta
