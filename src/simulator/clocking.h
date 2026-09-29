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

// §14.13 (printed page 366): a value a clocking block keeps between the event
// that sampled it and the reads of it -- a sampled input, the step and edge
// records its skews read, a drive's value -- whole: its width and its unknown
// bits with every word. The words are the value's own, held off the arena,
// because the step records are rewritten every time step. Kept as a
// `uint64_t`, a clockvar read 4'b1x0z as 1000 and lost every bit above 63.
struct ClockingValue {
  uint32_t width = 0;
  std::vector<Logic4Word> words;

  static ClockingValue Of(const Logic4Vec& v);
  // A known value of 64 bits, the form a caller holding a number gives.
  static ClockingValue Known(uint64_t value);
  Logic4Vec ToVec(Arena& arena) const;
  // The value's low 64 bits with an unknown bit read as 0, as
  // Logic4Vec::ToUint64 reads one.
  uint64_t Low() const;
};

// §14.16 (printed pages 368-369): one synchronous drive -- the block and the
// clockvar it drives, the value its right-hand side evaluated to where it ran,
// its cycle delay, and, for a bit-select or slice of the clockvar, the select
// of the signal it assigns in place of the whole signal (null otherwise).
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
  // §14.3's clocking_decl_assign: the signal an `= expression` names in place
  // of the module signal of the clockvar's own name, `output d = top.d`, as
  // the path it spells, hierarchical or not; empty where there is none.
  std::string_view target_path;
  // §14.5 (printed pages 357-358): the expression an `= expression` names
  // where it is no name -- a slice, `output nib = q[3:0]`, or a concatenation,
  // `input instr = {opcode, regA, regB[3:1]}` -- which an input samples and an
  // output drives in the block's instance; null where the clockvar is a
  // signal of its own name or of target_path.
  const Expr* target_expr = nullptr;
  ClockingDir direction = ClockingDir::kInput;
  SimTime skew{0};
  bool is_explicit_zero_skew = false;
  // §14.4: an input skew of 1step samples the signal's value as it stood
  // immediately before the clock edge (the previous time step's value).
  bool is_one_step_skew = false;
  // §14.3 (printed pages 355-356): a skew written as an edge of the clock,
  // `input negedge d` or `output negedge q`. An input so skewed is sampled at
  // that edge preceding the clocking event, and an output so skewed is driven
  // at that edge following it; kNone where the skew is no edge.
  Edge sample_edge = Edge::kNone;
  Edge drive_edge = Edge::kNone;
};

// §25.5.5 and §25.9.1 (printed pages 791-792 and 803): a clocking block is a
// member of the interface declaring it, reached through every name denoting
// the instance -- the instance's own path, `b1.sb`, an interface port bound to
// it, or a virtual interface holding it, `vif.sb`. The block `block_expr`
// names, the `X.sb` of a clockvar `X.sb.m`, or a bare `cb`; null where it names
// no registered block. Only the block's own path reached it, so a clockvar
// through a virtual interface read nothing and a drive through any path but a
// bare name was dropped.
const struct ClockingBlock* ResolveClockingBlockOf(const Expr* block_expr,
                                                   SimContext& ctx);

// §14.13: a clockvar read -- `cb.data` by the bare block name its module
// declared, or `X.sb.data` through a path to an interface instance -- yields
// the value the block sampled rather than the signal's live value. True with
// `out` filled when the access named a clockvar. Defined in clocking.cpp for
// the member-access read (EvalMemberAccess).
bool TryClockvarMemberAccess(std::string_view base_name,
                             std::string_view field_name, SimContext& ctx,
                             Arena& arena, Logic4Vec& out);
bool TryClockvarPathRead(const Expr* expr, SimContext& ctx, Arena& arena,
                         Logic4Vec& out);

// §23.9: the design-wide name of one signal a clocking block names. A block
// declares its clock and its signals by the bare names of the module it stands
// in, so two instances of one module declare signals spelled identically and
// the instance prefix is what tells the two variables apart -- the same thing
// PathDelay::inst_prefix does for a specify block's terminals. A block declared
// in a module elaborated as a top carries no prefix and the bare name is the
// whole of it.
std::string ClockingSignalName(std::string_view inst_prefix,
                               std::string_view signal_name);

struct ClockingBlock {
  // The name the block is registered under, which carries the instance prefix
  // of the module instance declaring it: §14.3 names a block within its module,
  // so two instances of one module declare two blocks of one name and only the
  // prefix separates them. The names below stay as the source wrote them, and
  // inst_prefix is what joins them to the instance's own variables.
  std::string_view name;
  std::string_view inst_prefix;
  std::string_view clock_signal;
  Edge clock_edge = Edge::kPosedge;
  // §14.3 with §9.4.2.3: the `iff` qualifier of the clocking event, null when
  // none was written. The block samples and its event fires only at the edges
  // where the condition holds, evaluated in the block's instance.
  const Expr* clock_iff = nullptr;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
  bool is_global = false;
};

class ClockingManager {
 public:
  void Register(ClockingBlock block);
  // §25.5.5: the block `target` also answers to `alias`, the name an
  // interface port of another instance spells it by, `tb.b1.sb` for the
  // `b1.sb` the port is bound to.
  void AddBlockAlias(std::string_view alias, std::string_view target) {
    block_aliases_[std::string(alias)] = std::string(target);
  }
  void Attach(SimContext& ctx, Scheduler& sched);
  const ClockingBlock* Find(std::string_view name) const;
  // §23.9: the block `name` reaches from where the reference stands. A clockvar
  // and an `always @(cb)` spell the block by the bare name its module declared,
  // so the running instance's own block is looked for first -- the one a
  // generate block the running process stands in declares ahead of the
  // module's (§27.4) -- and the bare name is the answer only where that
  // instance declared none, which is the whole of it for a block declared in a
  // module elaborated as a top.
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
  // §14.16: a drive the manager places, as ClockvarDrive describes it.
  void ScheduleOutputDrive(const ClockvarDrive& drive, SimContext& ctx,
                           Scheduler& sched);
  // §14.16 (printed pages 368-369): a synchronous drive `cb.v <= ##N r`
  // carries `value`, evaluated where the drive ran, and updates its signal N
  // cycles of the block after the drive's governing event -- the event it
  // runs coincident with, or else the next one -- plus the output skew. A
  // count of 0 is no delay, the drive ScheduleOutputDrive places.
  void ScheduleCycleDelayedDrive(const ClockvarDrive& drive, SimContext& ctx,
                                 Scheduler& sched);
  // §14.15: the name the sample variable of clockvar `signal_name` of the
  // block registered as `block_name` is created under, `$clockvar.b1.sb.gnt`.
  // No source spells it, so a reference to the clockvar is never read through
  // it -- an assertion's clockvar, already a sampled value, would read its own
  // snapshot of the variable a cycle late -- and a wait on the clockvar
  // watches it by this name (ExecWait).
  static std::string SampleVariableName(std::string_view block_name,
                                        std::string_view signal_name) {
    return "$clockvar." + std::string(block_name) + "." +
           std::string(signal_name);
  }
  void SampleInput(std::string_view block_name, std::string_view signal_name,
                   uint64_t value);
  // §14.13: the whole value an input clockvar sampled, or null before its
  // first clocking event.
  void SampleInputValue(std::string_view block_name,
                        std::string_view signal_name, ClockingValue value);
  const ClockingValue* GetSampledVec(std::string_view block_name,
                                     std::string_view signal_name) const;
  // The signal `signal_name` of `block`, or null where it declares none.
  const ClockingSignal* FindBlockSignal(const ClockingBlock& block,
                                        std::string_view signal_name) const {
    return FindSignal(block, signal_name);
  }
  // §14.5: `sig`'s expression as the block's instance reads it.
  static Logic4Vec EvalClockvarExpr(const ClockingBlock& block,
                                    const ClockingSignal& sig, SimContext& ctx);
  uint32_t Count() const { return static_cast<uint32_t>(blocks_.size()); }

  void SetDefaultClocking(std::string_view name) { default_clocking_ = name; }
  std::string_view GetDefaultClocking() const { return default_clocking_; }
  // §14.12 (printed page 361): a default clocking is the default within its
  // own module, interface, program or checker, so each instance keeps its own,
  // under the prefix its names carry, and a cycle delay reads the one of the
  // instance its process runs in; the last one set stands for a scope that
  // declared none. One default for the design let the last instance lowered
  // clock every `##`.
  void SetScopeDefaultClocking(std::string_view inst_prefix,
                               std::string_view name) {
    scope_default_clocking_[std::string(inst_prefix)] = name;
  }
  std::string_view DefaultClockingFor(const SimContext& ctx) const;

  void SetGlobalClocking(std::string_view name) { global_clocking_ = name; }
  std::string_view GetGlobalClocking() const { return global_clocking_; }

  void SetBlockEventVar(std::string_view block_name, Variable* var);

  // §14.11: a wait on the clocking block events of `block_name`, called once
  // per event from the Observed region, where the event fires, until it
  // answers false. A cycle delay's wait answers false once it resumes its
  // process, and is then gone: kept, it went on counting on the counter it had
  // freed.
  using EdgeCallback = std::function<bool()>;
  void RegisterEdgeWait(std::string_view block_name, EdgeCallback wait);

  // A callback called at every clocking block event of `block_name`.
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
  // The variable standing for clockvar `signal_name` of `block`: the sample
  // variable of an input, the signal of an output.
  Variable* ClockvarVariable(const ClockingBlock& block,
                             std::string_view signal_name,
                             SimContext& ctx) const;
  // §25.5.5 and §25.9.1 with §14.3: the block a path names, as the source
  // spelled it or as a virtual interface resolved it -- `b1.sb`, or
  // `top.b1.sb` headed by the top module's name -- from the running scope, or
  // null where none is registered under it.
  const ClockingBlock* FindByPath(std::string_view path,
                                  const SimContext& ctx) const;

  // §14.13: record what each clocking input holds at the end of the time step
  // now finishing, which is the value a 1step skew samples at the next clocking
  // event -- the clause puts it "at the Postponed region of the time step skew
  // time units prior to the clocking event". Attach installs this as the
  // end-of-step pass; nothing else writes what it records.
  void RecordStepValues(SimContext& ctx);
  // The value `signal_name` held at the end of the previous time step, or
  // nothing when no step has ended since Attach -- before the first one there
  // is no preceding step, and §14.4's "last value immediately before the
  // corresponding clock edge" is the value the signal still holds.
  const ClockingValue* PrevStepValue(std::string_view signal_name) const;
  // §14.4: the value `signal_name` held at the end of the last time step at or
  // before `t`, which is what an input with a numeric skew samples at time
  // `t` = edge - skew; nothing where no step has ended since Attach.
  const ClockingValue* ValueAtTime(std::string_view signal_name,
                                   SimTime t) const;
  // §14.3: what an edge-skewed input of `block_name` held at the last edge of
  // its skew, nothing before the first such edge.
  void RecordEdgeSample(std::string_view block_name,
                        std::string_view signal_name, ClockingValue value);
  const ClockingValue* EdgeSample(std::string_view block_name,
                                  std::string_view signal_name) const;

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
  // When a drive lands: at the next `edge` of `clock` for an output skewed by
  // an edge, else in the Re-NBA region of `drive_time`.
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
  // §14.4: what each clocking input held at the end of the last time step to
  // finish. Written only by RecordStepValues, because Variable::prev_value is
  // the §9.4.2 event controls' field -- their awaiters seed and resync it for
  // their own arming, so it answers whatever the design's other event controls
  // happen to have left there and answers nothing at all where none is armed.
  std::unordered_map<std::string, ClockingValue> prev_step_values_;
  // §14.4: what each input with a numeric skew held at the end of each time
  // step, oldest first, reaching back as far as the largest such skew and one
  // step beyond. RecordStepValues writes it beside prev_step_values_.
  std::unordered_map<std::string,
                     std::vector<std::pair<SimTime, ClockingValue>>>
      step_history_;
  // The largest numeric input skew of any block, which is how far back any
  // history is read: one signal's history serves every block sampling it.
  SimTime history_reach_{0};
  std::unordered_map<SampleKey, ClockingValue, PairHash> edge_samples_;
  // §14.15: the variable holding each input clockvar's sampled value, which
  // an event control on the clockvar watches (CreateSampleVariables).
  std::unordered_map<SampleKey, Variable*, PairHash> sample_vars_;
};

}  // namespace delta
