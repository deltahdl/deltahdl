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
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;
class SimContext;
struct Variable;

// §14.16: a synchronous drive always schedules its new value in the Re-NBA
// region. For a zero-skew output with no cycle delay it is the Re-NBA region of
// the current time step; for a nonzero skew or a nonzero cycle delay it is the
// Re-NBA region of a future time step. The region is Re-NBA in both cases --
// only the target time step differs.
Region SynchronousDriveRegion();

// §14.16: a synchronous drive executed coincident with its clocking event takes
// effect at that event; one executed at any other time performs its drive
// action as if it had run at the next clocking event. In both cases the driven
// signal updates `skew` after that governing event. Returns the time step at
// which the value updates.
SimTime SynchronousDriveEffectiveTime(SimTime now, bool event_now,
                                      SimTime next_event_time, SimTime skew);

// §14.16: when a clocking-block output's target is a net, an implicit driver is
// created on that net with (strong1, strong0) drive strength.
DriverStrength ClockvarNetDriverStrength();

// §14.16: that implicit net driver is initialized to 'z, so it has no influence
// on its target net until the first synchronous drive to the clockvar occurs.
Logic4Vec MakeClockvarNetDriverInit(Arena& arena, uint32_t width);

enum class ClockingDir : uint8_t {
  kInput,
  kOutput,
  kInout,
};

struct ClockingSignal {
  std::string_view signal_name;
  ClockingDir direction = ClockingDir::kInput;
  SimTime skew{0};
  bool is_explicit_zero_skew = false;
  // §14.4: an input skew of 1step samples the signal's value as it stood
  // immediately before the clock edge (the previous time step's value).
  bool is_one_step_skew = false;
};

struct ClockingBlock {
  std::string_view name;
  std::string_view clock_signal;
  Edge clock_edge = Edge::kPosedge;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
  bool is_global = false;
};

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

  void SetDefaultClocking(std::string_view name) { default_clocking_ = name; }
  std::string_view GetDefaultClocking() const { return default_clocking_; }

  void SetGlobalClocking(std::string_view name) { global_clocking_ = name; }
  std::string_view GetGlobalClocking() const { return global_clocking_; }

  void SetBlockEventVar(std::string_view block_name, Variable* var);

  void RegisterEdgeCallback(std::string_view block_name, SimContext& ctx,
                            Scheduler& sched, std::function<void()> cb);

  void NotifyBlockEvent(std::string_view block_name);
  void InvokeEdgeCallbacks(std::string_view block_name);

  // Records that the clocking block event for `block_name` fired at time `t`.
  void MarkBlockEventTime(std::string_view block_name, SimTime t);

  // True when the most recent clocking block event for `block_name` happened
  // exactly at time `t`.
  bool DidBlockEventOccurAt(std::string_view block_name, SimTime t) const;

  // §14.11: a ##0 cycle delay continues without suspension only when the
  // associated clocking block event has already occurred in the current time
  // step; otherwise it must suspend until that event. Returns true when the
  // delay may proceed immediately at time `now`.
  bool ZeroCycleDelayProceeds(std::string_view block_name, SimTime now) const;

  Variable* ResolveClockingMember(std::string_view block_name,
                                  std::string_view signal_name,
                                  SimContext& ctx) const;

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
  std::unordered_map<std::string, SimTime> last_event_time_;
};

}  // namespace delta
