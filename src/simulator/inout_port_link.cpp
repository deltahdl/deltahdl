#include "simulator/inout_port_link.h"

#include <cstddef>
#include <memory>
#include <optional>
#include <string>
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

struct InoutPortLink {
  InoutPortLinkEnds ends;
  ContAssignDriver to_outer;
  ContAssignDriver to_inner;
  ScratchNet toward_inner;
  std::vector<std::shared_ptr<InterconnectSchedule>> per_driver;
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

bool IsOwnSlot(const ContAssignDriver& drv, std::size_t slot) {
  return !drv.first && drv.driver_idx == slot;
}

DriverStrength PassedStrength(const NetStrength& s) {
  DriverStrength out;
  if (s.s0_hi != Strength::kHighz) out.s0 = s.s0_hi;
  if (s.s1_hi != Strength::kHighz) out.s1 = s.s1_hi;
  out.s0_lo = s.s0_lo;
  out.s1_lo = s.s1_lo;
  return out;
}

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

void GrowShadow(InoutPortLink& link, std::size_t slot, Arena& arena) {
  Net& shadow = link.toward_inner.net;
  while (shadow.drivers.size() <= slot) {
    shadow.drivers.push_back(
        MakeAllHighZ(arena, link.toward_inner.resolved.value.width));
    shadow.driver_strengths.emplace_back();
    link.per_driver.push_back(std::make_shared<InterconnectSchedule>());
  }
}

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
  if (ends.inner.type == NetType::kInterconnect)
    ends.inner.type = ends.outer.type;
  auto link = std::make_shared<InoutPortLink>(std::move(ends), ctx.GetArena());
  link->ends.outer.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryIn(link, slot, ctx); });
  link->ends.inner.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryOut(*link, slot, ctx); });
}

std::string SdfHierName(const std::string& dotted) {
  std::string out = dotted;
  for (char& c : out) {
    if (c == '.') c = '/';
  }
  return out;
}

}  // namespace delta
