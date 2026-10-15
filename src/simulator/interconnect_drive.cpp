// §32.4.4's interconnect delay at run time: a port connection's source change
// carried to its load across the delay annotated between them, with §30.7's
// pulse handling, which interconnect delays share with specify path delays.

#include "simulator/interconnect_drive.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// Schedules `transition` to arrive at the load. Its arrival does nothing, and
// does not advance time, once the transition is superseded.
void ScheduleArrival(const std::shared_ptr<InterconnectSchedule>& schedule,
                     const std::shared_ptr<InterconnectTransition>& transition,
                     SimContext& ctx,
                     const std::function<void(const Logic4Vec&)>& commit) {
  Event* arrival = ctx.GetScheduler().GetEventPool().Acquire();
  arrival->superseded = transition->superseded;
  arrival->callback = [schedule, transition, commit]() {
    if (*transition->superseded) return;
    std::erase(schedule->pending, transition);
    commit(transition->value);
  };
  ctx.GetScheduler().ScheduleEvent(SimTime{transition->ticks}, Region::kActive,
                                   arrival);
}

// What a transition arriving at `arrives` through Table 32-4's slot `slot`
// makes of the last transition still pending: whether that one is dropped --
// crossed by the new one (§30.7.4.2), or rejected with it as a pulse too
// narrow for the reject limit (§30.7) -- or stays, turned to x where the pulse
// falls between the two limits. A limit above the delay behaves as one at it
// (§32.7).
bool DropsLastPending(InterconnectTransition& last, uint64_t arrives,
                      const InterconnectDelay& delay, uint8_t slot,
                      Arena& arena) {
  if (IsNegativePulse(last.ticks, arrives)) return true;
  const uint64_t kDelay = delay.delays[slot];
  const PulseClassification kClass =
      ClassifyPulse(arrives - last.ticks,
                    EffectivePulseLimit(delay.reject_limit[slot], kDelay),
                    EffectivePulseLimit(delay.error_limit[slot], kDelay));
  if (kClass == PulseClassification::kReject) return true;
  if (kClass == PulseClassification::kForceX) {
    last.value = MakeAllX(arena, last.value.width);
    last.bits = MakeAllX(arena, last.bits.width);
  }
  return false;
}

}  // namespace

void DriveAcrossInterconnect(
    const std::shared_ptr<InterconnectSchedule>& schedule,
    const InterconnectDelay& delay, const InterconnectChange& change,
    SimContext& ctx, const std::function<void(const Logic4Vec&)>& commit) {
  auto& pending = schedule->pending;
  const uint64_t kNow = ctx.CurrentTime().ticks;
  for (;;) {
    // Where the load is heading: the last transition still on its way, or the
    // load as it stands where none is.
    const Logic4Vec& from =
        pending.empty() ? change.held : pending.back()->bits;
    if (from.SameValueAs(change.bits)) return;
    const uint8_t kSlot = ModulePathTransitionSlot(from, change.bits);
    const uint64_t kArrives = kNow + delay.delays[kSlot];
    if (!pending.empty() && DropsLastPending(*pending.back(), kArrives, delay,
                                             kSlot, ctx.GetArena())) {
      *pending.back()->superseded = true;
      pending.pop_back();
      continue;
    }
    if (kArrives == kNow && pending.empty()) {
      commit(change.value);
      return;
    }
    auto transition = std::make_shared<InterconnectTransition>();
    transition->ticks = kArrives;
    transition->value = change.value;
    transition->bits = change.bits;
    pending.push_back(transition);
    ScheduleArrival(schedule, transition, ctx, commit);
    return;
  }
}

namespace {

// What one load following a net's drivers holds on to: the net, the load's
// shadow of it, the load's name and how its connection commits.
struct InterconnectFollow {
  Net& net;
  std::shared_ptr<InterconnectShadow> shadow;
  std::string load;
  std::function<void(const Logic4Vec&)> commit;
};

// The shadow's slots for the net's drivers up to `slot`, each starting at the
// value the net's driver holds.
void GrowShadow(const InterconnectFollow& follow, std::size_t slot) {
  InterconnectShadow& shadow = *follow.shadow;
  while (shadow.net.drivers.size() <= slot) {
    const std::size_t kNext = shadow.net.drivers.size();
    shadow.net.drivers.push_back(follow.net.drivers[kNext]);
    shadow.net.driver_strengths.push_back(follow.net.driver_strengths[kNext]);
    shadow.per_driver.push_back(std::make_shared<InterconnectSchedule>());
  }
}

// A write of the net's driver `slot`, carried to the load's shadow.
void FollowDriver(const std::shared_ptr<InterconnectFollow>& follow,
                  std::size_t slot, SimContext& ctx) {
  InterconnectShadow& shadow = *follow->shadow;
  if (!shadow.alive) return;
  GrowShadow(*follow, slot);
  const Logic4Vec& value = follow->net.drivers[slot];
  const DriverStrength kStrength = follow->net.driver_strengths[slot];
  const SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr ||
      !mgr->HasSourceSpecificInterconnectDelay(follow->load)) {
    shadow.net.drivers[slot] = value;
    shadow.net.driver_strengths[slot] = kStrength;
    return;
  }
  const std::string_view kPort = slot < follow->net.driver_ports.size()
                                     ? follow->net.driver_ports[slot]
                                     : std::string_view();
  const InterconnectDelay* delay =
      mgr->FindInterconnectDelay(kPort, follow->load);
  const auto kArrive = [follow, slot, kStrength, &ctx](const Logic4Vec& v) {
    InterconnectShadow& arrived = *follow->shadow;
    if (!arrived.alive) return;
    arrived.net.drivers[slot] = v;
    arrived.net.driver_strengths[slot] = kStrength;
    arrived.net.Resolve(ctx.GetArena());
    follow->commit(arrived.resolved.value);
  };
  DriveAcrossInterconnect(
      shadow.per_driver[slot], delay == nullptr ? InterconnectDelay{} : *delay,
      InterconnectChange{shadow.net.drivers[slot], value, value}, ctx, kArrive);
}

}  // namespace

void FollowNetDrivers(Net& net,
                      const std::shared_ptr<InterconnectShadow>& shadow,
                      std::string load, SimContext& ctx,
                      std::function<void(const Logic4Vec&)> commit) {
  shadow->net.type = net.type;
  shadow->net.resolved = &shadow->resolved;
  const uint32_t kWidth =
      net.resolved == nullptr ? 1U : net.resolved->value.width;
  shadow->resolved.value = MakeLogic4Vec(ctx.GetArena(), kWidth);
  auto follow = std::make_shared<InterconnectFollow>(
      InterconnectFollow{net, shadow, std::move(load), std::move(commit)});
  // A driver the net already carries starts the shadow where it stands, so
  // its next write is measured from there; a source that moved before the
  // load began following it would otherwise look unmoved.
  if (!net.drivers.empty()) GrowShadow(*follow, net.drivers.size() - 1);
  net.driver_listeners.emplace_back(
      [follow, &ctx](std::size_t slot) { FollowDriver(follow, slot, ctx); });
}

}  // namespace delta
