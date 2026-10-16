#include "simulator/inout_port_link.h"

#include <cstddef>
#include <memory>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/interconnect_drive.h"
#include "simulator/lowerer_contassign_driver.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// A net standing apart from the design that resolves what one side of the
// link passes to the other, of the type and width of the net it stands for.
struct ScratchNet {
  Net net;
  Variable resolved;

  ScratchNet(const Net& like, Arena& arena) {
    net.type = like.type;
    net.resolve_hook = like.resolve_hook;
    net.resolved = &resolved;
    resolved.value = MakeAllHighZ(arena, like.resolved->value.width);
  }
};

// One link: the driver it holds on each net, allocated when it first carries
// something, and what each direction resolves.
struct InoutPortLink {
  InoutPortLinkEnds ends;
  ContAssignDriver to_outer;
  ContAssignDriver to_inner;
  // `outer`'s drivers as they have reached the port, each across the delay
  // from the source it stands for, the link's own driver held at high
  // impedance.
  ScratchNet toward_inner;
  std::vector<std::shared_ptr<InterconnectSchedule>> per_driver;
  // `inner`'s drivers but the link's own.
  ScratchNet toward_outer;

  InoutPortLink(InoutPortLinkEnds e, Arena& arena)
      : ends(std::move(e)),
        toward_inner(ends.outer, arena),
        toward_outer(ends.inner, arena) {
    to_outer.net = &ends.outer;
    to_outer.origin = ends.inner_origin;
    to_outer.source_port = ends.port;
    to_inner.net = &ends.inner;
    to_inner.origin = ends.outer_origin;
  }
};

// Whether `slot` of the net `drv` writes is the link's own driver there.
bool IsOwnSlot(const ContAssignDriver& drv, std::size_t slot) {
  return !drv.first && drv.driver_idx == slot;
}

// §28.12: a value passes through a port at the strengths it has, which are
// what the net it is resolved on reports, a range of §28.12.2 down to its
// lower end; a side the resolution reports at high impedance, as a net that
// computes no strength reports both, keeps the driver's default, so that the
// value still reaches the other net.
DriverStrength PassedStrength(const NetStrength& s) {
  DriverStrength out;
  if (s.s0_hi != Strength::kHighz) out.s0 = s.s0_hi;
  if (s.s1_hi != Strength::kHighz) out.s1 = s.s1_hi;
  out.s0_lo = s.s0_lo;
  out.s1_lo = s.s1_lo;
  return out;
}

// Writes what `from` resolved to into the link's driver `drv`, the slot
// added first where the link has none on that net yet, so the net's
// listeners, the link's own among them, already know it for the link's own.
void Commit(ContAssignDriver& drv, const ScratchNet& from, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  if (drv.first) {
    drv.driver_idx = drv.net->drivers.size();
    drv.net->drivers.push_back(
        MakeAllHighZ(arena, drv.net->resolved->value.width));
    drv.net->driver_strengths.emplace_back();
    drv.first = false;
  }
  ApplyContAssignToNet(
      drv, {from.resolved.value, PassedStrength(from.net.resolved_strength)},
      &ctx.GetScheduler(), arena);
}

// Toward the connection: `inner`'s drivers but the link's own, at once.
void CarryOut(InoutPortLink& link, std::size_t slot, SimContext& ctx) {
  if (IsOwnSlot(link.to_inner, slot)) return;
  Arena& arena = ctx.GetArena();
  Net& scratch = link.toward_outer.net;
  scratch.drivers = link.ends.inner.drivers;
  scratch.driver_strengths = link.ends.inner.driver_strengths;
  if (!link.to_inner.first) {
    scratch.drivers[link.to_inner.driver_idx] =
        MakeAllHighZ(arena, link.toward_outer.resolved.value.width);
  }
  scratch.Resolve(arena);
  Commit(link.to_outer, link.toward_outer, ctx);
}

// The shadow's slots up to `slot`, each new one starting at high impedance,
// which a driver held until its first write.
void GrowShadow(InoutPortLink& link, std::size_t slot, Arena& arena) {
  Net& shadow = link.toward_inner.net;
  while (shadow.drivers.size() <= slot) {
    shadow.drivers.push_back(
        MakeAllHighZ(arena, link.toward_inner.resolved.value.width));
    shadow.driver_strengths.emplace_back();
    link.per_driver.push_back(std::make_shared<InterconnectSchedule>());
  }
}

// Toward the port: a write of `outer`'s driver `slot`, carried across the
// delay annotated to the port from the source the driver stands for, or, for
// one standing for no port, from the connection. ApplyContAssignToNet records
// the slot's port before it tells a listener, and Lowerer::Lower acquires the
// manager before anything runs.
void CarryIn(const std::shared_ptr<InoutPortLink>& link, std::size_t slot,
             SimContext& ctx) {
  if (IsOwnSlot(link->to_outer, slot)) return;
  GrowShadow(*link, slot, ctx.GetArena());
  const Net& outer = link->ends.outer;
  const Logic4Vec& value = outer.drivers[slot];
  const DriverStrength kStrength = outer.driver_strengths[slot];
  const std::string_view kPort = outer.driver_ports[slot];
  const std::optional<InterconnectDelay> kDelay =
      ctx.AcquireSpecifyManager().ConnectionInterconnectDelay(
          kPort.empty() ? std::string_view(link->ends.source) : kPort,
          link->ends.load);
  const auto kArrive = [link, slot, kStrength, &ctx](const Logic4Vec& v) {
    Net& shadow = link->toward_inner.net;
    shadow.drivers[slot] = v;
    shadow.driver_strengths[slot] = kStrength;
    shadow.Resolve(ctx.GetArena());
    Commit(link->to_inner, link->toward_inner, ctx);
  };
  DriveAcrossInterconnect(
      link->per_driver[slot], kDelay.value_or(InterconnectDelay{}),
      InterconnectChange{link->toward_inner.net.drivers[slot], value, value},
      ctx, kArrive);
}

}  // namespace

void LinkInoutPortNets(InoutPortLinkEnds ends, SimContext& ctx) {
  auto link = std::make_shared<InoutPortLink>(std::move(ends), ctx.GetArena());
  link->ends.outer.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryIn(link, slot, ctx); });
  link->ends.inner.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryOut(*link, slot, ctx); });
}

}  // namespace delta
