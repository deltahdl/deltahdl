// §30.7's pulse filtering, applied to the driver of a module path output.
//
// The delay itself is only half of what a module path does. §30.7 opens by
// saying that "two consecutive scheduled transitions closer together in time
// than the module path delay are deemed a pulse", and then that the reject and
// error limits belonging to the delay forming the pulse's trailing edge decide
// whether it reaches the output, reaches it as x, or does not appear at all.
// Figure 30-5 is the worked case: with `(A => Y) = 7, 9;` a pulse of width 4 on
// A leaves a pulse of width 2 at Y, which is less than the rise delay's reject
// limit of 7, so nothing appears on Y.
//
// The pulse is detected the same way §28's inertial delay detects one: the
// driver is re-evaluated while a transition is still pending, and the value it
// now wants is the value already on the output. What §30.7 adds is that this is
// not automatically a cancellation. It is one of three outcomes, and the limits
// say which.
//
// A fourth stands beside those three. §30.7.4.2's negative pulse is what
// unequal delays make when the two schedules cross, and it has no width for a
// limit to be measured against; the showcancelled mode decides it instead.
//
// The selection of the delay and the limits is in
// src/simulator/module_path_delay.cpp; this file spends them.

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/module_path_delay.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/stmt_result.h"

namespace delta {

static bool SameValue(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.width != b.width || a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

static uint64_t TicksUntil(uint64_t target, const SimContext& ctx) {
  uint64_t now = ctx.CurrentTime().ticks;
  return target > now ? target - now : 0;
}

// What one transition of the path output costs and what governs a pulse ending
// on it. §30.6 settles the module path delay against the delay the driver
// already carried by taking the larger of the two, which is what
// SelectEffectivePathDelay answers. The limits come from the module path even
// where the distributed delay is the larger, because §30.6 speaks about the
// delay alone and §30.7.3 annotates the limits onto the module path transition
// delay; a driver no module path reaches keeps its own delay and no limits,
// which leaves it on §28's inertial route.
struct ModulePathTransitionDelay {
  uint64_t ticks = 0;
  uint64_t reject_limit = 0;
  uint64_t error_limit = 0;
};

static ModulePathTransitionDelay ResolveTransitionDelay(
    const ModulePathDrive& drive, const Logic4Vec& from, const Logic4Vec& to) {
  ModulePathDelay mp = SelectModulePathDelay(drive, from, to);
  if (!mp.found) return {drive.distributed_ticks, 0, 0};
  return {SelectEffectivePathDelay(mp.delay, drive.distributed_ticks),
          mp.reject_limit, mp.error_limit};
}

// §30.7.4.2's negative pulse: the two schedules cross, so there is no pulse of
// any width to measure. `target` is when the later of the two was scheduled for
// and `trailing` the earlier; `settled` is the value the output already holds
// and returns to.
//
// Without showcancelled the answer is that "the leading edge is cancelled. No
// transition takes place when the initial and final states of the pulse are the
// same, leaving no indication a schedule was ever present", which is a return
// that drives nothing. With it, "this style causes the leading edge to be
// scheduled to X and the trailing edge to be scheduled from X" -- the two edges
// being the output's own, in time order, so the x begins at the earlier
// schedule and the output leaves it at the later. Figure 30-7 is the case:
// `(in => out) = (4, 6);` with `in` falling at 10 and rising at 11 schedules
// `out` low at 16 and high at 15, and showcancelled shows x across 15 to 16 --
// or from 11, the moment of detection, under on-detect.
static ExecTask DriveCancelledPulse(const ModulePathDrive& drive,
                                    const Logic4Vec& settled, SimTime target,
                                    uint64_t trailing, bool* committed) {
  SimContext& ctx = drive.ctx;
  // `trailing` is what ScheduleNegativePulse calls the scheduled leading time.
  // The two names agree: its parameter means the edge that comes first at the
  // output, and for a negative pulse that is the schedule computed last.
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

// Carries out §30.7's answer for one pulse. `leading` is the value the pending
// transition would have placed on the output and `settled` the value already
// there, which the driver has now returned to; `target` is when the leading
// edge was scheduled for, so the pulse runs from `target` to the trailing
// edge.
//
// A negative pulse has no width to measure and is handed to
// DriveCancelledPulse above before the measurement is reached.
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

  // Past that test the trailing edge is no earlier than the leading one, so the
  // width is their difference and never a clamp of one.
  uint64_t width = trailing - target.ticks;

  PulseClassification cls =
      ClassifyPulse(width, trail.reject_limit, trail.error_limit);
  if (cls == PulseClassification::kReject) co_return StmtResult::kDone;

  if (cls == PulseClassification::kForceX) {
    // §30.7.4.1: on-event leaves the x transition at the time the leading edge
    // was already scheduled for, on-detect advances it to now, the moment the
    // pulse was detected. The style is asked for by the instance-qualified
    // output name, which is what RegisterPulseStyles in
    // src/simulator/specify_register.cpp filed the declaration under, so a
    // pulsestyle declared in one instance of a cell does not answer for
    // another.
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

ExecTask RunModulePathTransition(const ModulePathDrive& drive,
                                 const Logic4Vec& old_val, Logic4Vec& val,
                                 bool* committed) {
  SimContext& ctx = drive.ctx;
  ModulePathTransitionDelay lead = ResolveTransitionDelay(drive, old_val, val);
  SimTime target = ctx.CurrentTime() + SimTime{lead.ticks};

  for (uint64_t remaining = TicksUntil(target.ticks, ctx); remaining > 0;
       remaining = TicksUntil(target.ticks, ctx)) {
    if (co_await InertialDelayAwaiter{ctx, remaining, drive.sources}) break;

    auto next = EvalExpr(drive.rhs, ctx, drive.arena, drive.width);
    if (SameValue(next, val)) continue;
    if (!SameValue(next, old_val)) {
      // The driver wants a different value than the one pending, so the pending
      // transition is dropped and the new one takes its own delay.
      val = next;
      lead = ResolveTransitionDelay(drive, old_val, val);
      target = ctx.CurrentTime() + SimTime{lead.ticks};
      continue;
    }

    // The driver has returned to the value already on the output before the
    // pending transition fired, which is §30.7's pulse. `val` becomes that
    // settled value so the caller's own commit, which runs whatever this
    // returns, places nothing new on the output.
    Logic4Vec leading = val;
    val = next;
    co_await FilterModulePathPulse(drive, leading, old_val, target, committed);
    co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
