#include "simulator/clocking.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

Region SynchronousDriveRegion() { return Region::kReNBA; }

SimTime SynchronousDriveEffectiveTime(SimTime now, bool event_now,
                                      SimTime next_event_time, SimTime skew) {
  // §14.16: a drive that runs coincident with its clocking event takes effect
  // at that event; a drive that runs at any other time still performs its
  // action as if it had run at the next clocking event. The driven signal then
  // updates `skew` after that governing event.
  SimTime governing_event = event_now ? now : next_event_time;
  return governing_event + skew;
}

DriverStrength ClockvarNetDriverStrength() {
  return DriverStrength{Strength::kStrong, Strength::kStrong};
}

Logic4Vec MakeClockvarNetDriverInit(Arena& arena, uint32_t width) {
  Logic4Vec v = MakeLogic4Vec(arena, width);
  uint32_t remaining = width;
  for (uint32_t i = 0; i < v.nwords; ++i) {
    uint32_t bits = remaining >= 64 ? 64 : remaining;
    uint64_t mask = (bits == 64) ? ~uint64_t{0} : ((uint64_t{1} << bits) - 1);
    // 'z is encoded as aval = 0, bval = 1 per valid bit.
    v.words[i].aval = 0;
    v.words[i].bval = mask;
    remaining -= bits;
  }
  return v;
}

ClockingValue ClockingValue::Of(const Logic4Vec& v) {
  ClockingValue held;
  held.width = v.width;
  held.words.assign(v.words, v.words + v.nwords);
  return held;
}

ClockingValue ClockingValue::Known(uint64_t value) {
  ClockingValue held;
  held.width = 64;
  held.words.push_back(Logic4Word{value, 0});
  return held;
}

Logic4Vec ClockingValue::ToVec(Arena& arena) const {
  Logic4Vec v = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < v.nwords && i < words.size(); ++i)
    v.words[i] = words[i];
  return v;
}

uint64_t ClockingValue::Low() const {
  return words.empty() ? 0 : words[0].aval & ~words[0].bval;
}

std::string ClockingSignalName(std::string_view inst_prefix,
                               std::string_view signal_name) {
  return std::string(inst_prefix) + std::string(signal_name);
}

// The path a clockvar's signal is spelled by: its `= expression` where the
// declaration gives one, its own name otherwise.
static std::string_view ClockvarPath(const ClockingSignal& sig) {
  return sig.target_path.empty() ? sig.signal_name : sig.target_path;
}

// The variable `path` names from the instance a clocking block was declared
// in. A bare name is that instance's own signal, found under its prefix
// (§23.9). §14.3 (printed page 354) with §23.6: a clocking event, and a
// clockvar's `= expression`, may name the signal hierarchically,
// `@(posedge top.clk)` and `output d = top.d`, which reaches nothing joined to
// the prefix, so it is resolved as a reference written in that instance is,
// SimContext::FindVariable walking the path from there, `$root` and a top
// module's name at its head included.
static Variable* FindInBlockInstance(std::string_view inst_prefix,
                                     std::string_view path, SimContext& ctx) {
  if (auto* var = ctx.FindVariable(ClockingSignalName(inst_prefix, path))) {
    return var;
  }
  if (path.find('.') == std::string_view::npos) return nullptr;
  InstancePrefixOverride in_block(ctx.InstancePrefixOverride(), inst_prefix);
  return ctx.FindVariable(path);
}

void ClockingManager::Register(ClockingBlock block) {
  name_index_[block.name] = blocks_.size();
  blocks_.push_back(std::move(block));
}

const ClockingBlock* ClockingManager::Find(std::string_view name) const {
  auto it = name_index_.find(name);
  if (it != name_index_.end()) return &blocks_[it->second];
  auto alias = block_aliases_.find(std::string(name));
  return alias != block_aliases_.end() ? Find(alias->second) : nullptr;
}

std::string_view ClockingManager::DefaultClockingFor(
    const SimContext& ctx) const {
  auto it = scope_default_clocking_.find(ctx.ActiveInstancePrefix());
  return it != scope_default_clocking_.end() ? it->second : default_clocking_;
}

const ClockingBlock* ClockingManager::FindInScope(std::string_view name,
                                                  const SimContext& ctx) const {
  const std::string kInstPrefix = ctx.ActiveInstancePrefix();
  // §23.9 with §27.4: a process in a generate block reaches the block its own
  // instance declares, registered under that instance's prefix, first.
  if (const Process* proc = ctx.CurrentProcess()) {
    for (const std::string& key :
         GenerateBlockKeys(kInstPrefix, proc->gen_prefixes, name)) {
      if (const auto* block = Find(key)) return block;
    }
  }
  if (const auto* block = Find(kInstPrefix + std::string(name))) return block;
  return Find(name);
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

// §14.10: whether the clock has just made the transition the block's clocking
// event names. `prev` is what this block last saw the clock at, kept by the
// watcher below rather than read from Variable::prev_value -- that field
// belongs to the §9.4.2 event controls, which seed and resync it for their own
// arming, so a clock no event control watches leaves it at its default and
// every notification looks like a posedge.
static bool CheckClockEdge(uint64_t prev, uint64_t cur, Edge edge) {
  if (edge == Edge::kPosedge) return prev == 0 && cur == 1;
  if (edge == Edge::kNegedge) return prev == 1 && cur == 0;
  return prev != cur;
}

// §14.10: what one block's clocking event is watched through -- the block whose
// event it is, the clock variable its clocking expression names, the signals it
// samples and the edge it waits for, and this block's record of what that clock
// last stood at. Held together because the watcher hands all of it on when it
// re-arms, and because §14.6 lets several blocks name one clock: each keeps its
// own record, so one block's event cannot consume the transition for the rest.
struct ClockWatch {
  std::string block_name;
  // §23.9: the instance the block was declared in, which is what joins the bare
  // signal names below to that instance's own variables. Empty for a block
  // declared in a module elaborated as a top.
  std::string inst_prefix;
  Variable* clk_var = nullptr;
  std::vector<ClockingSignal> signals;
  Edge edge = Edge::kPosedge;
  std::shared_ptr<uint64_t> last_clock;
  const Expr* iff = nullptr;
};

// §14.3 with §9.4.2.3: whether the clocking event's `iff` qualifier lets this
// edge through. §12.4 decides what true means, so any bit at 1 passes and a
// zero, x or z condition does not. The condition names the block's instance's
// variables, so it is evaluated from that instance.
static bool ClockIffHolds(const ClockWatch& watch, SimContext& ctx) {
  if (watch.iff == nullptr) return true;
  if (watch.inst_prefix.empty()) {
    return EvalExpr(watch.iff, ctx, ctx.GetArena()).IsTruthy();
  }
  InstancePrefixOverride in_block(ctx.InstancePrefixOverride(),
                                  watch.inst_prefix);
  return EvalExpr(watch.iff, ctx, ctx.GetArena()).IsTruthy();
}

// §14.5: `expr` read from the instance `inst_prefix` names, where a bare
// name is that instance's own signal.
static Logic4Vec EvalInBlockInstance(std::string_view inst_prefix,
                                     const Expr* expr, SimContext& ctx) {
  if (inst_prefix.empty()) return EvalExpr(expr, ctx, ctx.GetArena());
  InstancePrefixOverride in_block(ctx.InstancePrefixOverride(), inst_prefix);
  return EvalExpr(expr, ctx, ctx.GetArena());
}

Logic4Vec ClockingManager::EvalClockvarExpr(const ClockingBlock& block,
                                            const ClockingSignal& sig,
                                            SimContext& ctx) {
  return EvalInBlockInstance(block.inst_prefix, sig.target_expr, ctx);
}

// §14.4 (printed page 356) with §14.3: the value input `sig` samples at this
// clocking event. An edge skew samples at that edge preceding the event, which
// the clock watcher recorded as it passed; a 1step skew samples the value at
// the end of the previous time step (§14.13 places it at that step's
// Postponed region); a numeric skew samples the signal that many time units
// before the event; any other samples it now. A record not yet made is the
// value the signal still holds. Sampled at the edge itself, `input #2 d` read
// the value d took at the edge.
static ClockingValue SampleOf(const ClockingManager* mgr,
                              const ClockWatch& watch,
                              const ClockingSignal& sig, const Variable& var,
                              SimContext& ctx) {
  const std::string kVarName =
      ClockingSignalName(watch.inst_prefix, ClockvarPath(sig));
  const ClockingValue* recorded = nullptr;
  if (sig.sample_edge != Edge::kNone) {
    recorded = mgr->EdgeSample(watch.block_name, sig.signal_name);
  } else if (sig.is_one_step_skew) {
    recorded = mgr->PrevStepValue(kVarName);
  } else if (sig.skew.ticks > 0) {
    SimTime now = ctx.CurrentTime();
    SimTime at{now.ticks > sig.skew.ticks ? now.ticks - sig.skew.ticks : 0};
    recorded = mgr->ValueAtTime(kVarName, at);
  }
  return recorded != nullptr ? *recorded : ClockingValue::Of(var.value);
}

// Whether input `sig` is sampled by the pass `only_zero_skew` names: an
// explicit #0 input in the Observed region's pass, every other input in the
// clock edge's.
static bool SampledInThisPass(const ClockingSignal& sig, bool only_zero_skew) {
  if (sig.direction != ClockingDir::kInput &&
      sig.direction != ClockingDir::kInout) {
    return false;
  }
  return sig.is_explicit_zero_skew == only_zero_skew;
}

static void SampleBlockInputs(ClockingManager* mgr, const ClockWatch& watch,
                              SimContext& ctx, bool only_zero_skew) {
  for (const auto& sig : watch.signals) {
    if (!SampledInThisPass(sig, only_zero_skew)) continue;
    // §14.5 (printed pages 357-358): a clockvar bound to an expression that
    // is no name samples that expression, a concatenation or a slice, whole.
    // With no variable of its name to read, it sampled nothing.
    if (sig.target_expr != nullptr) {
      mgr->SampleInputValue(watch.block_name, sig.signal_name,
                            ClockingValue::Of(EvalInBlockInstance(
                                watch.inst_prefix, sig.target_expr, ctx)));
      continue;
    }
    auto* var = FindInBlockInstance(watch.inst_prefix, ClockvarPath(sig), ctx);
    if (!var) continue;
    mgr->SampleInputValue(watch.block_name, sig.signal_name,
                          SampleOf(mgr, watch, sig, *var, ctx));
  }
}

static void RegisterClockWatcher(ClockingManager* mgr, const ClockWatch& watch,
                                 SimContext& ctx, Scheduler& sched);

// Watch the clock for the next notification, reading the block back so a change
// to what it samples is picked up. A block that is gone is not re-armed.
static void RearmClockWatcher(ClockingManager* mgr, const ClockWatch& watch,
                              SimContext& ctx, Scheduler& sched) {
  const auto* blk = mgr->Find(watch.block_name);
  if (blk == nullptr) return;
  RegisterClockWatcher(mgr,
                       ClockWatch{watch.block_name, watch.inst_prefix,
                                  watch.clk_var, blk->signals, blk->clock_edge,
                                  watch.last_clock, blk->clock_iff},
                       ctx, sched);
}

// §14.13: when its clocking event is processed, a clocking block refreshes its
// sampled values first and only then triggers its own block event. The
// inputs carrying a skew are sampled here, and the explicit #0 ones in the
// Observed region alongside the event itself, which §14.4 is what puts there.
static void FireClockingEvent(ClockingManager* mgr, const ClockWatch& watch,
                              SimContext& ctx, Scheduler& sched) {
  SampleBlockInputs(mgr, watch, ctx, false);
  auto* ev = sched.GetEventPool().Acquire();
  // The watch is captured by value because the callback runs in the Observed
  // region, after this function and the caller that owns the watch have both
  // returned.
  ev->callback = [mgr, watch, &ctx, &sched]() {
    SampleBlockInputs(mgr, watch, ctx, true);
    mgr->MarkBlockEventTime(watch.block_name, sched.CurrentTime());
    mgr->NotifyBlockEvent(watch.block_name);
    mgr->InvokeEdgeCallbacks(watch.block_name);
  };
  sched.ScheduleEvent(sched.CurrentTime(), Region::kObserved, ev);
}

// §14.3 (printed pages 355-356): each input whose skew is an edge of the
// clock takes the value it holds as the clock makes that edge, which the
// next clocking event samples.
static void RecordEdgeSkewedInputs(ClockingManager* mgr,
                                   const ClockWatch& watch, uint64_t prev,
                                   uint64_t cur, SimContext& ctx) {
  for (const auto& sig : watch.signals) {
    if (sig.sample_edge == Edge::kNone ||
        sig.direction == ClockingDir::kOutput ||
        !CheckClockEdge(prev, cur, sig.sample_edge)) {
      continue;
    }
    if (auto* var =
            FindInBlockInstance(watch.inst_prefix, ClockvarPath(sig), ctx)) {
      mgr->RecordEdgeSample(watch.block_name, sig.signal_name,
                            ClockingValue::Of(var->value));
    }
  }
}

static void RegisterClockWatcher(ClockingManager* mgr, const ClockWatch& watch,
                                 SimContext& ctx, Scheduler& sched) {
  Variable* clk_var = watch.clk_var;
  clk_var->AddWatcher([mgr, watch, &ctx, &sched]() {
    uint64_t cur = watch.clk_var->value.ToUint64() & 1;
    RecordEdgeSkewedInputs(mgr, watch, *watch.last_clock, cur, ctx);
    // §14.3 (printed pages 354-355) with §15.5: a named event is a clocking
    // event of its own, `clocking cb @(e)`, and its trigger notifies the
    // variable without changing a value, so each notification is one. Asked
    // for an edge, it never fired.
    bool fired = (watch.clk_var->is_event ||
                  CheckClockEdge(*watch.last_clock, cur, watch.edge)) &&
                 ClockIffHolds(watch, ctx);
    // Recorded whether or not the transition was the one this block waits for,
    // because it is what the clock now stands at either way.
    *watch.last_clock = cur;
    if (fired) FireClockingEvent(mgr, watch, ctx, sched);
    RearmClockWatcher(mgr, watch, ctx, sched);
    return true;
  });
}

void ClockingManager::RecordStepValues(SimContext& ctx) {
  for (const auto& block : blocks_) {
    for (const auto& sig : block.signals) {
      if (sig.direction == ClockingDir::kOutput) continue;
      // §23.9: what is recorded is the instance's own variable, so two
      // instances of one module keep two records rather than overwriting each
      // other's under the bare name the module declared.
      std::string name =
          ClockingSignalName(block.inst_prefix, ClockvarPath(sig));
      auto* var =
          FindInBlockInstance(block.inst_prefix, ClockvarPath(sig), ctx);
      if (var == nullptr) continue;
      ClockingValue value = ClockingValue::Of(var->value);
      if (sig.skew.ticks > 0 && !sig.is_one_step_skew) {
        RecordHistory(step_history_[name], ctx.CurrentTime(), value,
                      history_reach_);
      }
      prev_step_values_[std::move(name)] = std::move(value);
    }
  }
}

// Appends what a signal held at the end of the step at `now` and drops the
// entries no skew of `reach` can reach back to, keeping the last one at or
// before the cutoff, which is the value standing there.
void ClockingManager::RecordHistory(
    std::vector<std::pair<SimTime, ClockingValue>>& history, SimTime now,
    ClockingValue value, SimTime reach) {
  if (!history.empty() && history.back().first == now) {
    history.back().second = std::move(value);
  } else {
    history.emplace_back(now, std::move(value));
  }
  uint64_t cutoff = now.ticks > reach.ticks ? now.ticks - reach.ticks : 0;
  size_t keep_from = 0;
  while (keep_from + 1 < history.size() &&
         history[keep_from + 1].first.ticks <= cutoff) {
    ++keep_from;
  }
  if (keep_from > 0) {
    history.erase(history.begin(),
                  history.begin() + static_cast<std::ptrdiff_t>(keep_from));
  }
}

const ClockingValue* ClockingManager::ValueAtTime(std::string_view signal_name,
                                                  SimTime t) const {
  auto it = step_history_.find(std::string(signal_name));
  if (it == step_history_.end() || it->second.empty()) return nullptr;
  const ClockingValue* found = &it->second.front().second;
  for (const auto& [time, value] : it->second) {
    if (time.ticks > t.ticks) break;
    found = &value;
  }
  return found;
}

const ClockingValue* ClockingManager::PrevStepValue(
    std::string_view signal_name) const {
  auto it = prev_step_values_.find(std::string(signal_name));
  return it != prev_step_values_.end() ? &it->second : nullptr;
}

void ClockingManager::Attach(SimContext& ctx, Scheduler& sched) {
  for (const auto& block : blocks_) {
    for (const auto& sig : block.signals) {
      if (sig.direction != ClockingDir::kOutput && !sig.is_one_step_skew &&
          sig.skew.ticks > history_reach_.ticks) {
        history_reach_ = sig.skew;
      }
    }
  }
  for (const auto& block : blocks_) {
    auto* clk_var =
        FindInBlockInstance(block.inst_prefix, block.clock_signal, ctx);
    if (!clk_var) continue;
    // §14.10: the block's event is the transition of its clocking expression,
    // so the record starts at what the clock stands at now -- a clock already
    // high when the block attaches has not made a posedge by being watched.
    auto last_clock = std::make_shared<uint64_t>(clk_var->value.ToUint64() & 1);
    RegisterClockWatcher(
        this,
        ClockWatch{std::string(block.name), std::string(block.inst_prefix),
                   clk_var, block.signals, block.clock_edge, last_clock,
                   block.clock_iff},
        ctx, sched);
  }
  CreateSampleVariables(ctx);
  // §14.13: a 1step input is the value of the signal at the Postponed region
  // of the step before the clocking event, so it is recorded as each step ends.
  sched.AddPostTimestepCallback([this, &ctx]() { RecordStepValues(ctx); });
}

void ClockingManager::RecordEdgeSample(std::string_view block_name,
                                       std::string_view signal_name,
                                       ClockingValue value) {
  edge_samples_[{std::string(block_name), std::string(signal_name)}] =
      std::move(value);
}

const ClockingValue* ClockingManager::EdgeSample(
    std::string_view block_name, std::string_view signal_name) const {
  auto it =
      edge_samples_.find({std::string(block_name), std::string(signal_name)});
  return it != edge_samples_.end() ? &it->second : nullptr;
}

void ClockingManager::SampleInput(std::string_view block_name,
                                  std::string_view signal_name,
                                  uint64_t value) {
  SampleInputValue(block_name, signal_name, ClockingValue::Known(value));
}

// §14.16 (printed page 368) with §10.7: `var` takes `held` as an assignment
// to it does, at its own width -- a narrower value zero-extended, a wider one
// truncated -- its unknown bits kept for a 4-state variable and cleared for a
// 2-state one (§6.11.2). Answers whether any bit changed.
static bool WriteDrivenValue(Variable* var, const ClockingValue& held) {
  bool changed = false;
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    Logic4Word w = i < held.words.size() ? held.words[i] : Logic4Word{};
    uint64_t mask = WordMaskWithinWidth(var->value.width, i);
    w.aval &= mask;
    w.bval = var->is_4state ? (w.bval & mask) : 0;
    if (!var->is_4state)
      w.aval &= ~(held.words.size() > i ? held.words[i].bval : 0);
    Logic4Word& cur = var->value.words[i];
    changed |= cur.aval != w.aval || cur.bval != w.bval;
    cur = w;
  }
  return changed;
}

void ClockingManager::SampleInputValue(std::string_view block_name,
                                       std::string_view signal_name,
                                       ClockingValue value) {
  SampleKey key{std::string(block_name), std::string(signal_name)};
  auto it = sample_vars_.find(key);
  Variable* held = it != sample_vars_.end() ? it->second : nullptr;
  bool changed = held != nullptr && WriteDrivenValue(held, value);
  sampled_values_[std::move(key)] = std::move(value);
  // §14.15 (printed page 367): an event control on the clockvar is told of a
  // change of the value it sampled, and of nothing else. It is told once the
  // sample is stored, because a process it wakes runs at once and reads the
  // clockvar: told first, `wait (s.sb.gnt == 1)` read the old sample and
  // slept on.
  if (changed) held->NotifyWatchers();
}

const ClockingValue* ClockingManager::GetSampledVec(
    std::string_view block_name, std::string_view signal_name) const {
  auto it =
      sampled_values_.find({std::string(block_name), std::string(signal_name)});
  return it != sampled_values_.end() ? &it->second : nullptr;
}

uint64_t ClockingManager::GetSampledValue(std::string_view block_name,
                                          std::string_view signal_name) const {
  const ClockingValue* held = GetSampledVec(block_name, signal_name);
  return held != nullptr ? held->Low() : 0;
}

void ClockingManager::ScheduleOutputDrive(std::string_view block_name,
                                          std::string_view signal_name,
                                          uint64_t value, SimContext& ctx,
                                          Scheduler& sched) {
  ScheduleOutputDrive(
      ClockvarDrive{block_name, signal_name, ClockingValue::Known(value)}, ctx,
      sched);
}

void ClockingManager::ScheduleOutputDrive(const ClockvarDrive& drive,
                                          SimContext& ctx, Scheduler& sched) {
  std::string_view block_name = drive.block_name;
  std::string_view signal_name = drive.signal_name;
  const ClockingValue& value = drive.value;
  const Expr* target = drive.target;
  const ClockingBlock* block = Find(block_name);
  if (block == nullptr) return;
  auto skew = GetOutputSkew(block_name, signal_name);
  auto now = sched.CurrentTime();
  // §14.16: place the drive relative to its governing clocking event. When the
  // clocking event is occurring in this time step the drive is coincident;
  // otherwise it performs as if at the next clocking event. This model invokes
  // the drive primitive at the event, so the next-event time falls back to the
  // current time when no future event time is tracked.
  bool event_now = DidBlockEventOccurAt(block_name, now);
  auto drive_time = SynchronousDriveEffectiveTime(now, event_now, now, skew);
  // §23.9: the signal a clockvar drives is the one the block's own instance
  // declared, or the one its `= expression` names from there, so the drive is
  // placed on that variable.
  const ClockingSignal* sig = FindSignal(*block, signal_name);
  // §14.3 (printed pages 355-356): an output skewed by an edge of the clock is
  // driven at that edge following the drive's clocking event.
  Variable* edge_clock =
      sig != nullptr && sig->drive_edge != Edge::kNone
          ? FindInBlockInstance(block->inst_prefix, block->clock_signal, ctx)
          : nullptr;
  DriveEdge when{edge_clock, sig != nullptr ? sig->drive_edge : Edge::kNone,
                 drive_time};
  // §14.5 (printed pages 357-358): an output bound to an expression, `output
  // nib = q[3:0]`, drives that expression, as an assignment to it from the
  // block's instance writes the slice alone. With no variable of its name,
  // the drive landed nowhere.
  if (target == nullptr && sig != nullptr) target = sig->target_expr;
  if (target != nullptr) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [target, prefix = block->inst_prefix, value, &ctx]() {
      std::optional<InstancePrefixOverride> in_block;
      if (!prefix.empty())
        in_block.emplace(ctx.InstancePrefixOverride(), prefix);
      Arena& arena = ctx.GetArena();
      PerformBlockingAssign(target, value.ToVec(arena), ctx, arena);
    };
    ScheduleDriveEvent(when, ev, sched);
    return;
  }
  auto* var = FindInBlockInstance(
      block->inst_prefix, sig != nullptr ? ClockvarPath(*sig) : signal_name,
      ctx);
  if (var == nullptr) return;
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [var, value]() {
    // §14.16 (printed page 368): the drive assigns the signal in the Re-NBA
    // region, and a change of a variable is the §9.4.2 event that a process
    // waiting on it, `always @(d)`, is woken by. Written without the notice,
    // the value landed and the process slept on.
    if (WriteDrivenValue(var, value)) var->NotifyWatchers();
  };
  ScheduleDriveEvent(when, ev, sched);
}

// §14.3 (printed pages 355-356): an output skewed by an edge of the clock is
// driven at that edge following the drive's clocking event, so the update
// waits for the clock to make it; taken for a zero skew, `output negedge q`
// was driven at the posedge. §14.16: any other drive is scheduled in the
// Re-NBA region of `drive_time`, a nonzero skew only shifting it into a future
// time step.
void ClockingManager::ScheduleDriveEvent(const DriveEdge& when, Event* ev,
                                         Scheduler& sched) {
  Variable* clk = when.clock;
  if (clk == nullptr) {
    sched.ScheduleEvent(when.drive_time, SynchronousDriveRegion(), ev);
    return;
  }
  auto last = std::make_shared<uint64_t>(clk->value.ToUint64() & 1);
  clk->AddWatcher([clk, last, edge = when.edge, ev, &sched]() {
    uint64_t cur = clk->value.ToUint64() & 1;
    bool hit = CheckClockEdge(*last, cur, edge);
    *last = cur;
    if (!hit) return false;
    sched.ScheduleEvent(sched.CurrentTime(), SynchronousDriveRegion(), ev);
    return true;
  });
}

void ClockingManager::ScheduleCycleDelayedDrive(const ClockvarDrive& drive,
                                                SimContext& ctx,
                                                Scheduler& sched) {
  std::string_view block_name = drive.block_name;
  uint32_t cycles = drive.cycles;
  // The governing event is this step's where it has occurred, and an event of
  // this step is then not one of the N; otherwise it is the next event, which
  // the wait counts before the N. §14.16 (printed page 369): a drive with no
  // cycle delay executed at any other time performs its drive action as if at
  // that next event, so it too waits for it; placed at once, `#3 cb.v <= r`
  // drove v at 3.
  SimTime start = sched.CurrentTime();
  bool event_now = DidBlockEventOccurAt(block_name, start);
  if (cycles == 0 && event_now) {
    ScheduleOutputDrive(drive, ctx, sched);
    return;
  }
  uint32_t remaining = event_now ? cycles : cycles + 1;
  RegisterEdgeWait(block_name, [this, drive, remaining, start, event_now, &ctx,
                                &sched]() mutable {
    if (event_now && sched.CurrentTime() == start) return true;
    if (--remaining > 0) return true;
    ScheduleOutputDrive(drive, ctx, sched);
    return false;
  });
}

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

void ClockingManager::RegisterEdgeWait(std::string_view block_name,
                                       EdgeCallback wait) {
  edge_callbacks_[std::string(block_name)].push_back(std::move(wait));
}

void ClockingManager::RegisterEdgeCallback(std::string_view block_name,
                                           SimContext&, Scheduler&,
                                           std::function<void()> cb) {
  RegisterEdgeWait(block_name, [cb = std::move(cb)]() {
    cb();
    return true;
  });
}

void ClockingManager::MarkBlockEventTime(std::string_view block_name,
                                         SimTime t) {
  last_event_time_[std::string(block_name)] = t;
}

bool ClockingManager::DidBlockEventOccurAt(std::string_view block_name,
                                           SimTime t) const {
  auto it = last_event_time_.find(std::string(block_name));
  if (it == last_event_time_.end()) return false;
  return it->second == t;
}

bool ClockingManager::ZeroCycleDelayProceeds(std::string_view block_name,
                                             SimTime now) const {
  return DidBlockEventOccurAt(block_name, now);
}

// §14.11: each wait on the block's events is told of this one. A wait resumes
// its process at once, and the process may reach another cycle delay and
// register a new wait before this returns, so the waits are taken out of the
// table before any is called: iterated in place, the registration grew the
// vector under the loop. The waits that go on waiting are put back ahead of
// the ones registered meanwhile, which this event does not count.
void ClockingManager::InvokeEdgeCallbacks(std::string_view block_name) {
  std::string key(block_name);
  auto it = edge_callbacks_.find(key);
  if (it == edge_callbacks_.end() || it->second.empty()) return;
  std::vector<EdgeCallback> waiting = std::move(it->second);
  it->second.clear();
  std::vector<EdgeCallback> kept;
  for (auto& cb : waiting) {
    if (cb()) kept.push_back(std::move(cb));
  }
  auto& registered = edge_callbacks_[key];
  for (auto& cb : registered) kept.push_back(std::move(cb));
  registered = std::move(kept);
}

const ClockingSignal* ClockingManager::FindSignal(
    const ClockingBlock& block, std::string_view signal_name) const {
  for (const auto& sig : block.signals) {
    if (sig.signal_name == signal_name) return &sig;
  }
  return nullptr;
}

Variable* ClockingManager::ResolveClockingMember(std::string_view block_name,
                                                 std::string_view signal_name,
                                                 SimContext& ctx) const {
  // §23.9: `cb.data` spells the block by the bare name its module declared, so
  // the running instance's own block is what it reaches.
  const auto* block = FindInScope(block_name, ctx);
  return block != nullptr ? ClockvarVariable(*block, signal_name, ctx)
                          : nullptr;
}

Variable* ClockingManager::ClockvarVariable(const ClockingBlock& block,
                                            std::string_view signal_name,
                                            SimContext& ctx) const {
  const auto* sig = FindSignal(block, signal_name);
  if (!sig) return nullptr;
  // §14.15: an input clockvar stands for its sampled value, which its sample
  // variable holds.
  auto held =
      sample_vars_.find({std::string(block.name), std::string(signal_name)});
  if (held != sample_vars_.end()) return held->second;
  return FindInBlockInstance(block.inst_prefix, ClockvarPath(*sig), ctx);
}

const ClockingBlock* ClockingManager::FindByPath(std::string_view path,
                                                 const SimContext& ctx) const {
  if (const auto* block = FindInScope(path, ctx)) return block;
  // A path headed by the top module's name, or by instances above the one
  // registered, is registered under its tail.
  for (size_t dot = path.find('.'); dot != std::string_view::npos;
       dot = path.find('.', dot + 1)) {
    if (const auto* block = Find(path.substr(dot + 1))) return block;
  }
  return nullptr;
}

const ClockingBlock* ResolveClockingBlockOf(const Expr* block_expr,
                                            SimContext& ctx) {
  auto* mgr = ctx.GetClockingManager();
  if (mgr == nullptr || block_expr == nullptr) return nullptr;
  if (block_expr->kind == ExprKind::kIdentifier) {
    return mgr->FindInScope(block_expr->text, ctx);
  }
  if (block_expr->kind != ExprKind::kMemberAccess ||
      block_expr->is_scope_resolution || block_expr->lhs == nullptr) {
    return nullptr;
  }
  std::string_view field =
      block_expr->rhs != nullptr &&
              block_expr->rhs->kind == ExprKind::kIdentifier
          ? block_expr->rhs->text
          : block_expr->text;
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(block_expr->lhs, ctx, ctx.GetArena());
  if (base.is_virtual_interface) {
    std::string name = VirtualInterfaceComponentName(base.handle, field, ctx);
    return name.empty() ? nullptr : mgr->FindByPath(name, ctx);
  }
  std::string path;
  BuildLhsName(block_expr, path);
  if (path.empty()) return nullptr;
  if (const auto* block = mgr->FindInScope(path, ctx)) return block;
  return mgr->Find(path);
}

// §14.15 (printed page 367): an event control on an input clockvar, `@(cb.d)`
// or `@(posedge cb.en)`, is synchronised to the clocking event, waking on a
// change of the value the clockvar sampled. So each input clockvar is given a
// variable holding that value, which SampleInputValue writes and notifies, and
// which starts at what the signal holds when the block is armed. Bound to the
// signal itself, the event control woke on a change between clocking events,
// a pulse the block never sampled among them.
void ClockingManager::CreateSampleVariables(SimContext& ctx) {
  for (const auto& block : blocks_) {
    for (const auto& sig : block.signals) {
      if (sig.direction == ClockingDir::kOutput) continue;
      Logic4Vec now;
      bool four_state = true;
      if (sig.target_expr != nullptr) {
        now = EvalClockvarExpr(block, sig, ctx);
      } else if (auto* var = FindInBlockInstance(block.inst_prefix,
                                                 ClockvarPath(sig), ctx)) {
        now = var->value;
        four_state = var->is_4state;
      } else {
        continue;
      }
      // Created under the clockvar's full name, `b1.sb.gnt`, so a wait on a
      // condition reading it finds it by name (ExecWait).
      auto* key = ctx.GetArena().Create<std::string>(
          SampleVariableName(block.name, sig.signal_name));
      auto* held = ctx.CreateVariable(*key, now.width);
      if (held == nullptr) held = ctx.GetArena().Create<Variable>();
      held->value = MakeLogic4Vec(ctx.GetArena(), now.width);
      held->is_4state = four_state;
      WriteDrivenValue(held, ClockingValue::Of(now));
      sample_vars_[{std::string(block.name), std::string(sig.signal_name)}] =
          held;
    }
  }
}

// §14.13: reading a clockvar (cb.data) yields the value sampled at the clocking
// block's most recent input event, not the signal's live value.
// ResolveClockingMember confirms `base_name` names a clocking block carrying
// signal `field_name` and yields the underlying variable for its width. Returns
// true and fills `out` when the access resolved to a clockvar.
static bool ReadClockvar(const ClockingBlock* block,
                         std::string_view field_name, SimContext& ctx,
                         Arena& arena, Logic4Vec& out) {
  auto* mgr = ctx.GetClockingManager();
  if (block == nullptr) return false;
  // §14.5 (printed pages 357-358): a clockvar bound to an expression that is
  // no name reads the whole value it sampled, at the expression's width; before
  // its first clocking event it has sampled nothing and reads x.
  const ClockingSignal* sig = mgr->FindBlockSignal(*block, field_name);
  if (sig != nullptr && sig->target_expr != nullptr) {
    if (const ClockingValue* held =
            mgr->GetSampledVec(block->name, field_name)) {
      out = held->ToVec(arena);
    } else {
      out = MakeAllX(
          arena, ClockingManager::EvalClockvarExpr(*block, *sig, ctx).width);
    }
    return true;
  }
  auto* sig_var = mgr->ClockvarVariable(*block, field_name, ctx);
  if (!sig_var) return false;
  // §14.13 (printed page 366): what was sampled, whole -- every word and the
  // unknown bits with them -- at the signal's width. Read back as 64 known
  // bits, 4'b1x0z read as 1000 and a 96-bit input lost its top word.
  if (const ClockingValue* held = mgr->GetSampledVec(block->name, field_name)) {
    ClockingValue fitted = *held;
    fitted.width = sig_var->value.width;
    out = fitted.ToVec(arena);
    return true;
  }
  out = MakeLogic4VecVal(arena, sig_var->value.width, 0);
  return true;
}

bool TryClockvarMemberAccess(std::string_view base_name,
                             std::string_view field_name, SimContext& ctx,
                             Arena& arena, Logic4Vec& out) {
  auto* mgr = ctx.GetClockingManager();
  if (!mgr) return false;
  // §23.9: `cb.data` spells the block by the bare name the module declared, so
  // the sampled value read back is the one belonging to the instance this
  // expression is running in, which is what the block was registered under.
  return ReadClockvar(mgr->FindInScope(base_name, ctx), field_name, ctx, arena,
                      out);
}

void ClockingManager::BindCheckerFormal(const Variable* formal,
                                        std::string block_name,
                                        std::string field) {
  checker_formals_[formal] = {std::move(block_name), std::move(field)};
}

const std::pair<std::string, std::string>* ClockingManager::CheckerFormal(
    const Variable* formal) const {
  auto it = checker_formals_.find(formal);
  return it == checker_formals_.end() ? nullptr : &it->second;
}

bool TryCheckerFormalClockvar(const Variable* formal, SimContext& ctx,
                              Arena& arena, Logic4Vec& out) {
  auto* mgr = ctx.GetClockingManager();
  const auto* bound = mgr != nullptr ? mgr->CheckerFormal(formal) : nullptr;
  if (bound == nullptr) return false;
  return ReadClockvar(mgr->Find(bound->first), bound->second, ctx, arena, out);
}

// §25.5.5 and §25.9.1 with §14.13: a clockvar reached through a path to its
// interface instance, `vif.sb.a` or a port's `b1.sb.a`, reads what that
// block sampled (ResolveClockingBlockOf). Only a path spelling the block's
// own registered name reached it, and one through a virtual interface read 0.
bool TryClockvarPathRead(const Expr* expr, SimContext& ctx, Arena& arena,
                         Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kMemberAccess ||
      ctx.GetClockingManager() == nullptr) {
    return false;
  }
  const ClockingBlock* block = ResolveClockingBlockOf(expr->lhs, ctx);
  if (block == nullptr) return false;
  std::string_view field =
      expr->rhs != nullptr && expr->rhs->kind == ExprKind::kIdentifier
          ? expr->rhs->text
          : expr->text;
  return ReadClockvar(block, field, ctx, arena, out);
}

}  // namespace delta
