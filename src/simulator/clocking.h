#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;
class SimContext;
struct Event;
struct Variable;

Region SynchronousDriveRegion();

SimTime SynchronousDriveEffectiveTime(SimTime now, bool event_now,
                                      SimTime next_event_time, SimTime skew);

DriverStrength ClockvarNetDriverStrength();

Logic4Vec MakeClockvarNetDriverInit(Arena& arena, uint32_t width);

struct ClockingValue {
  uint32_t width = 0;
  std::vector<Logic4Word> words;

  static ClockingValue Of(const Logic4Vec& v);
  static ClockingValue Known(uint64_t value);
  Logic4Vec ToVec(Arena& arena) const;
  uint64_t Low() const;
};

struct ClockvarDrive {
  std::string_view block_name;
  std::string_view signal_name;
  ClockingValue value;
  uint32_t cycles = 0;
  const Expr* target = nullptr;
};

enum class ClockingDir : uint8_t {
  kInput,
  kOutput,
  kInout,
};

struct ClockingSignal {
  std::string_view signal_name;
  std::string_view target_path;
  const Expr* target_expr = nullptr;
  ClockingDir direction = ClockingDir::kInput;
  SimTime skew{0};
  bool is_explicit_zero_skew = false;
  bool is_one_step_skew = false;
  Edge sample_edge = Edge::kNone;
  Edge drive_edge = Edge::kNone;
};

const struct ClockingBlock* ResolveClockingBlockOf(const Expr* block_expr,
                                                   SimContext& ctx);

bool TryClockvarMemberAccess(std::string_view base_name,
                             std::string_view field_name, SimContext& ctx,
                             Arena& arena, Logic4Vec& out);
bool TryCheckerFormalClockvar(const Variable* formal, SimContext& ctx,
                              Arena& arena, Logic4Vec& out);
bool TryClockvarPathRead(const Expr* expr, SimContext& ctx, Arena& arena,
                         Logic4Vec& out);

std::string ClockingSignalName(std::string_view inst_prefix,
                               std::string_view signal_name);

struct ClockingBlock {
  std::string_view name;
  std::string_view inst_prefix;
  std::string_view clock_signal;
  Edge clock_edge = Edge::kPosedge;
  const Expr* clock_iff = nullptr;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
  bool is_global = false;
};

class ClockingManager {
 public:
  void Register(ClockingBlock block);
  void AddBlockAlias(std::string_view alias, std::string_view target) {
    block_aliases_[std::string(alias)] = std::string(target);
  }
  void Attach(SimContext& ctx, Scheduler& sched);
  const ClockingBlock* Find(std::string_view name) const;
  const ClockingBlock* FindInScope(std::string_view name,
                                   const SimContext& ctx) const;
  SimTime GetInputSkew(std::string_view block_name,
                       std::string_view signal_name) const;
  SimTime GetOutputSkew(std::string_view block_name,
                        std::string_view signal_name) const;
  uint64_t GetSampledValue(std::string_view block_name,
                           std::string_view signal_name) const;
  void ScheduleOutputDrive(std::string_view block_name,
                           std::string_view signal_name, uint64_t value,
                           SimContext& ctx, Scheduler& sched);
  void ScheduleOutputDrive(const ClockvarDrive& drive, SimContext& ctx,
                           Scheduler& sched);
  void ScheduleCycleDelayedDrive(const ClockvarDrive& drive, SimContext& ctx,
                                 Scheduler& sched);
  static std::string SampleVariableName(std::string_view block_name,
                                        std::string_view signal_name) {
    return "$clockvar." + std::string(block_name) + "." +
           std::string(signal_name);
  }
  void SampleInput(std::string_view block_name, std::string_view signal_name,
                   uint64_t value);
  void SampleInputValue(std::string_view block_name,
                        std::string_view signal_name, ClockingValue value);
  const ClockingValue* GetSampledVec(std::string_view block_name,
                                     std::string_view signal_name) const;
  const ClockingSignal* FindBlockSignal(const ClockingBlock& block,
                                        std::string_view signal_name) const {
    return FindSignal(block, signal_name);
  }
  static Logic4Vec EvalClockvarExpr(const ClockingBlock& block,
                                    const ClockingSignal& sig, SimContext& ctx);
  uint32_t Count() const { return static_cast<uint32_t>(blocks_.size()); }

  void SetDefaultClocking(std::string_view name) { default_clocking_ = name; }
  std::string_view GetDefaultClocking() const { return default_clocking_; }
  void SetScopeDefaultClocking(std::string_view inst_prefix,
                               std::string_view name) {
    scope_default_clocking_[std::string(inst_prefix)] = name;
  }
  std::string_view DefaultClockingFor(const SimContext& ctx) const;

  void SetGlobalClocking(std::string_view name) { global_clocking_ = name; }
  std::string_view GetGlobalClocking() const { return global_clocking_; }

  void SetBlockEventVar(std::string_view block_name, Variable* var);
  bool IsBlockEventVar(const Variable* var) const;

  using EdgeCallback = std::function<bool()>;
  void RegisterEdgeWait(std::string_view block_name, EdgeCallback wait);

  void RegisterEdgeCallback(std::string_view block_name, SimContext& ctx,
                            Scheduler& sched, std::function<void()> cb);

  void NotifyBlockEvent(std::string_view block_name);
  void InvokeEdgeCallbacks(std::string_view block_name);

  void MarkBlockEventTime(std::string_view block_name, SimTime t);

  bool DidBlockEventOccurAt(std::string_view block_name, SimTime t) const;

  bool ZeroCycleDelayProceeds(std::string_view block_name, SimTime now) const;

  Variable* ResolveClockingMember(std::string_view block_name,
                                  std::string_view signal_name,
                                  SimContext& ctx) const;
  Variable* ClockvarVariable(const ClockingBlock& block,
                             std::string_view signal_name,
                             SimContext& ctx) const;
  const ClockingBlock* FindByPath(std::string_view path,
                                  const SimContext& ctx) const;

  void RecordStepValues(SimContext& ctx);
  const ClockingValue* PrevStepValue(std::string_view signal_name) const;
  const ClockingValue* ValueAtTime(std::string_view signal_name,
                                   SimTime t) const;
  void RecordEdgeSample(std::string_view block_name,
                        std::string_view signal_name, ClockingValue value);
  const ClockingValue* EdgeSample(std::string_view block_name,
                                  std::string_view signal_name) const;
  void BindCheckerFormal(const Variable* formal, std::string block_name,
                         std::string field);
  const std::pair<std::string, std::string>* CheckerFormal(
      const Variable* formal) const;

 private:
  using SampleKey = std::pair<std::string, std::string>;
  struct PairHash {
    size_t operator()(const SampleKey& p) const {
      auto h1 = std::hash<std::string>{}(p.first);
      auto h2 = std::hash<std::string>{}(p.second);
      return h1 ^ (h2 << 1);
    }
  };

  void CreateSampleVariables(SimContext& ctx);
  struct DriveEdge {
    Variable* clock = nullptr;
    Edge edge = Edge::kNone;
    SimTime drive_time{0};
  };
  static void ScheduleDriveEvent(const DriveEdge& when, Event* ev,
                                 Scheduler& sched);
  static void RecordHistory(
      std::vector<std::pair<SimTime, ClockingValue>>& history, SimTime now,
      ClockingValue value, SimTime reach);
  const ClockingSignal* FindSignal(const ClockingBlock& block,
                                   std::string_view signal_name) const;

  std::vector<ClockingBlock> blocks_;
  std::unordered_map<std::string_view, size_t> name_index_;
  std::unordered_map<std::string, std::string> block_aliases_;
  std::unordered_map<SampleKey, ClockingValue, PairHash> sampled_values_;
  std::string_view default_clocking_;
  std::unordered_map<std::string, std::string_view> scope_default_clocking_;
  std::string_view global_clocking_;
  std::unordered_map<std::string_view, Variable*> block_event_vars_;
  std::unordered_map<std::string, std::vector<EdgeCallback>> edge_callbacks_;
  std::unordered_map<std::string, SimTime> last_event_time_;
  std::unordered_map<std::string, ClockingValue> prev_step_values_;
  std::unordered_map<std::string,
                     std::vector<std::pair<SimTime, ClockingValue>>>
      step_history_;
  SimTime history_reach_{0};
  std::unordered_map<SampleKey, ClockingValue, PairHash> edge_samples_;
  std::unordered_map<SampleKey, Variable*, PairHash> sample_vars_;
  std::unordered_map<const Variable*, SampleKey> checker_formals_;
};

}  // namespace delta
