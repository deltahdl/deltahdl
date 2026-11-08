#include <cstdint>

#include "common/types.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/stmt_result.h"

namespace delta {

static uint64_t TicksUntil(uint64_t target, const SimContext& ctx) {
  uint64_t now = ctx.CurrentTime().ticks;
  return target > now ? target - now : 0;
}

struct ModulePathTransitionDelay {
  uint64_t ticks = 0;
  uint64_t reject_limit = 0;
  uint64_t error_limit = 0;
};

static ModulePathTransitionDelay ResolveTransitionDelay(
    const ModulePathDrive& drive, const Logic4Vec& from, const Logic4Vec& to) {
  ModulePathDelay mp = SelectModulePathDelay(drive, from, to);
  if (!mp.found) return {drive.distributed_ticks, 0, 0};
  uint64_t delay = mp.delay;
  if (drive.at_port) {
    const uint64_t kSpent = drive.ctx.CurrentTime().ticks - mp.source_ticks;
    delay = delay > kSpent ? delay - kSpent : 0;
  }
  return {SelectEffectivePathDelay(delay, drive.distributed_ticks),
          mp.reject_limit, mp.error_limit};
}

static ExecTask DriveCancelledPulse(const ModulePathDrive& drive,
                                    const Logic4Vec& settled, SimTime target,
                                    uint64_t trailing, bool* committed) {
  SimContext& ctx = drive.ctx;
  NegativePulseSchedule neg =
      ScheduleNegativePulse(drive.mgr.ResolveShowCancelled(drive.output),
                            drive.mgr.ResolvePulseStyle(drive.output),
                            ctx.CurrentTime().ticks, trailing);
  if (!neg.force_x) co_return StmtResult::kDone;

  uint64_t to_x = TicksUntil(neg.x_time, ctx);
  if (to_x > 0) co_await DelayAwaiter{ctx, to_x};
  drive.commit(MakeAllX(drive.arena, settled.width));

  uint64_t to_settled = TicksUntil(target.ticks, ctx);
  if (to_settled > 0) co_await DelayAwaiter{ctx, to_settled};
  drive.commit(settled);
  *committed = true;
  co_return StmtResult::kDone;
}

static ExecTask FilterModulePathPulse(const ModulePathDrive& drive,
                                      const Logic4Vec& leading,
                                      const Logic4Vec& settled, SimTime target,
                                      bool* committed) {
  SimContext& ctx = drive.ctx;
  ModulePathTransitionDelay trail =
      ResolveTransitionDelay(drive, leading, settled);
  uint64_t trailing = ctx.CurrentTime().ticks + trail.ticks;
  if (IsNegativePulse(target.ticks, trailing)) {
    co_await DriveCancelledPulse(drive, settled, target, trailing, committed);
    co_return StmtResult::kDone;
  }

  uint64_t width = trailing - target.ticks;

  PulseClassification cls =
      ClassifyPulse(width, trail.reject_limit, trail.error_limit);
  if (cls == PulseClassification::kReject) co_return StmtResult::kDone;

  if (cls == PulseClassification::kForceX) {
    uint64_t x_at =
        FilteredPulseLeadingXTime(drive.mgr.ResolvePulseStyle(drive.output),
                                  ctx.CurrentTime().ticks, target.ticks);
    uint64_t to_x = TicksUntil(x_at, ctx);
    if (to_x > 0) co_await DelayAwaiter{ctx, to_x};
    drive.commit(MakeAllX(drive.arena, settled.width));
  } else {
    uint64_t to_lead = TicksUntil(target.ticks, ctx);
    if (to_lead > 0) co_await DelayAwaiter{ctx, to_lead};
    drive.commit(leading);
  }

  uint64_t to_trail = TicksUntil(trailing, ctx);
  if (to_trail > 0) co_await DelayAwaiter{ctx, to_trail};
  drive.commit(settled);
  *committed = true;
  co_return StmtResult::kDone;
}

namespace {

class PendingPathValue {
 public:
  PendingPathValue(Net* net, const Logic4Vec& v) : net_(net) { Hold(v); }
  PendingPathValue(const PendingPathValue&) = delete;
  PendingPathValue& operator=(const PendingPathValue&) = delete;
  PendingPathValue(PendingPathValue&&) = delete;
  PendingPathValue& operator=(PendingPathValue&&) = delete;
  ~PendingPathValue() {
    if (net_ != nullptr) net_->pending_path_value.reset();
  }

  void Hold(const Logic4Vec& v) const {
    if (net_ != nullptr) net_->pending_path_value = v;
  }

 private:
  Net* net_;
};

}  // namespace

ExecTask RunModulePathTransition(const ModulePathDrive& drive,
                                 const Logic4Vec& old_val, Logic4Vec& val,
                                 bool* committed) {
  SimContext& ctx = drive.ctx;
  const PendingPathValue kPending(ctx.FindNet(drive.output), val);
  ModulePathTransitionDelay lead = ResolveTransitionDelay(drive, old_val, val);
  SimTime scheduled = ctx.CurrentTime();
  SimTime target = scheduled + SimTime{lead.ticks};

  for (uint64_t remaining = TicksUntil(target.ticks, ctx); remaining > 0;
       remaining = TicksUntil(target.ticks, ctx)) {
    if (co_await InertialDelayAwaiter{ctx, remaining, drive.sources}) break;

    auto next = EvalExpr(drive.rhs, ctx, drive.arena, drive.width);
    if (next.SameValueAs(val)) {
      if (ctx.CurrentTime().ticks == scheduled.ticks) {
        lead = ResolveTransitionDelay(drive, old_val, val);
        target = scheduled + SimTime{lead.ticks};
      }
      continue;
    }
    if (!next.SameValueAs(old_val)) {
      val = next;
      kPending.Hold(val);
      lead = ResolveTransitionDelay(drive, old_val, val);
      target = ctx.CurrentTime() + SimTime{lead.ticks};
      continue;
    }

    Logic4Vec leading = val;
    val = next;
    co_await FilterModulePathPulse(drive, leading, old_val, target, committed);
    co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
