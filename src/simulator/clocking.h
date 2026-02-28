#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

class Scheduler;
class SimContext;
struct Variable;

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
// ClockingBlock: a named clocking block with default skews (S14)
// =============================================================================

struct ClockingBlock {
  std::string_view name;
  std::string_view clock_signal;
  Edge clock_edge = Edge::kPosedge;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
  bool is_global = false;
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

  // S14.12: Default clocking block.
  void SetDefaultClocking(std::string_view name) { default_clocking_ = name; }
  std::string_view GetDefaultClocking() const { return default_clocking_; }

  // S14.13: Global clocking block.
  void SetGlobalClocking(std::string_view name) { global_clocking_ = name; }
  std::string_view GetGlobalClocking() const { return global_clocking_; }

  // S14.8: Associate a named-event Variable with a clocking block.
  void SetBlockEventVar(std::string_view block_name, Variable* var);

  // Register a callback invoked on each clock edge of the given block.
  void RegisterEdgeCallback(std::string_view block_name, SimContext& ctx,
                            Scheduler& sched, std::function<void()> cb);

  // Notify event variable and invoke edge callbacks (used by watcher).
  void NotifyBlockEvent(std::string_view block_name);
  void InvokeEdgeCallbacks(std::string_view block_name);

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
  std::string_view default_clocking_;
  std::string_view global_clocking_;
  std::unordered_map<std::string_view, Variable*> block_event_vars_;
  std::unordered_map<std::string, std::vector<std::function<void()>>>
      edge_callbacks_;
};

}  // namespace delta
