#include "simulator/clocking.h"

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

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

static void SampleBlockInputs(ClockingManager* mgr, const std::string& name,
                              const std::vector<ClockingSignal>& signals,
                              SimContext& ctx, bool only_zero_skew) {
  for (const auto& sig : signals) {
    bool is_input = (sig.direction == ClockingDir::kInput ||
                     sig.direction == ClockingDir::kInout);
    if (!is_input) continue;
    if (only_zero_skew && !sig.is_explicit_zero_skew) continue;
    if (!only_zero_skew && sig.is_explicit_zero_skew) continue;
    auto* var = ctx.FindVariable(sig.signal_name);
    if (!var) continue;
    // §14.4: an input skew of 1step "indicates that the signal is to be
    // sampled at the end of the previous time step ... the value sampled is
    // always the signal's last value immediately before the corresponding clock
    // edge", which §14.13 places at the Postponed region of that step. That is
    // what the end-of-step record holds. Before any step has ended there is no
    // preceding one, and the value the signal still holds is the value it held
    // immediately before this edge.
    uint64_t sampled = var->value.ToUint64();
    if (sig.is_one_step_skew) {
      sampled = mgr->PrevStepValue(sig.signal_name).value_or(sampled);
    }
    mgr->SampleInput(name, sig.signal_name, sampled);
  }
}

// §14.10: what one block's clocking event is watched through -- the block whose
// event it is, the clock variable its clocking expression names, the signals it
// samples and the edge it waits for, and this block's record of what that clock
// last stood at. Held together because the watcher hands all of it on when it
// re-arms, and because §14.6 lets several blocks name one clock: each keeps its
// own record, so one block's event cannot consume the transition for the rest.
struct ClockWatch {
  std::string block_name;
  Variable* clk_var = nullptr;
  std::vector<ClockingSignal> signals;
  Edge edge = Edge::kPosedge;
  std::shared_ptr<uint64_t> last_clock;
};

static void RegisterClockWatcher(ClockingManager* mgr, ClockWatch watch,
                                 SimContext& ctx, Scheduler& sched);

// Watch the clock for the next notification, reading the block back so a change
// to what it samples is picked up. A block that is gone is not re-armed.
static void RearmClockWatcher(ClockingManager* mgr, const ClockWatch& watch,
                              SimContext& ctx, Scheduler& sched) {
  const auto* blk = mgr->Find(watch.block_name);
  if (blk == nullptr) return;
  RegisterClockWatcher(mgr,
                       ClockWatch{watch.block_name, watch.clk_var, blk->signals,
                                  blk->clock_edge, watch.last_clock},
                       ctx, sched);
}

// §14.13: "Upon processing its specified clocking event, a clocking block shall
// update its sampled values before triggering the clocking block event." The
// inputs carrying a skew are sampled here, and the explicit #0 ones in the
// Observed region alongside the event itself, which §14.4 is what puts there.
static void FireClockingEvent(ClockingManager* mgr, const ClockWatch& watch,
                              SimContext& ctx, Scheduler& sched) {
  SampleBlockInputs(mgr, watch.block_name, watch.signals, ctx, false);
  auto* ev = sched.GetEventPool().Acquire();
  auto name = watch.block_name;
  auto signals = watch.signals;
  ev->callback = [mgr, name, signals, &ctx, &sched]() {
    SampleBlockInputs(mgr, name, signals, ctx, true);
    mgr->MarkBlockEventTime(name, sched.CurrentTime());
    mgr->NotifyBlockEvent(name);
    mgr->InvokeEdgeCallbacks(name);
  };
  sched.ScheduleEvent(sched.CurrentTime(), Region::kObserved, ev);
}

static void RegisterClockWatcher(ClockingManager* mgr, ClockWatch watch,
                                 SimContext& ctx, Scheduler& sched) {
  Variable* clk_var = watch.clk_var;
  clk_var->AddWatcher([mgr, watch, &ctx, &sched]() {
    uint64_t cur = watch.clk_var->value.ToUint64() & 1;
    bool fired = CheckClockEdge(*watch.last_clock, cur, watch.edge);
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
      auto* var = ctx.FindVariable(sig.signal_name);
      if (var == nullptr) continue;
      prev_step_values_[std::string(sig.signal_name)] = var->value.ToUint64();
    }
  }
}

std::optional<uint64_t> ClockingManager::PrevStepValue(
    std::string_view signal_name) const {
  auto it = prev_step_values_.find(std::string(signal_name));
  if (it == prev_step_values_.end()) return std::nullopt;
  return it->second;
}

void ClockingManager::Attach(SimContext& ctx, Scheduler& sched) {
  for (const auto& block : blocks_) {
    auto* clk_var = ctx.FindVariable(block.clock_signal);
    if (!clk_var) continue;
    // §14.10: the block's event is the transition of its clocking expression,
    // so the record starts at what the clock stands at now -- a clock already
    // high when the block attaches has not made a posedge by being watched.
    auto last_clock = std::make_shared<uint64_t>(clk_var->value.ToUint64() & 1);
    RegisterClockWatcher(
        this,
        ClockWatch{std::string(block.name), clk_var, block.signals,
                   block.clock_edge, last_clock},
        ctx, sched);
  }
  // §14.13: a 1step input is the value of the signal at the Postponed region
  // of the step before the clocking event, so it is recorded as each step ends.
  sched.AddPostTimestepCallback([this, &ctx]() { RecordStepValues(ctx); });
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
  auto now = sched.CurrentTime();
  // §14.16: place the drive relative to its governing clocking event. When the
  // clocking event is occurring in this time step the drive is coincident;
  // otherwise it performs as if at the next clocking event. This model invokes
  // the drive primitive at the event, so the next-event time falls back to the
  // current time when no future event time is tracked.
  bool event_now = DidBlockEventOccurAt(block_name, now);
  auto drive_time = SynchronousDriveEffectiveTime(now, event_now, now, skew);
  auto sig_name = std::string(signal_name);
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&ctx, sig_name, value]() {
    auto* var = ctx.FindVariable(sig_name);
    if (!var) return;
    var->value.words[0].aval = value;
    var->value.words[0].bval = 0;
  };

  // §14.16: the new value is scheduled in the Re-NBA region regardless of
  // skew; a nonzero skew only shifts drive_time into a future time step.
  sched.ScheduleEvent(drive_time, SynchronousDriveRegion(), ev);
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

void ClockingManager::RegisterEdgeCallback(std::string_view block_name,
                                           SimContext&, Scheduler&,
                                           std::function<void()> cb) {
  auto bn = std::string(block_name);
  edge_callbacks_[bn].push_back(std::move(cb));
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

Variable* ClockingManager::ResolveClockingMember(std::string_view block_name,
                                                 std::string_view signal_name,
                                                 SimContext& ctx) const {
  const auto* block = Find(block_name);
  if (!block) return nullptr;
  const auto* sig = FindSignal(*block, signal_name);
  if (!sig) return nullptr;
  return ctx.FindVariable(sig->signal_name);
}

}  // namespace delta
