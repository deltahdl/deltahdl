#include "simulator/inout_port_link.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/interconnect_drive.h"
#include "simulator/lowerer_child.h"
#include "simulator/lowerer_contassign_driver.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"
#include "simulator/statement_assign.h"
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

// Where `partial`, bits [outer_lo, outer_lo + width) of a link's outer net
// joined to bits [inner_lo, inner_lo + width) of its inner one, none where the
// width is zero; otherwise the two whole nets.
struct LinkBits {
  uint32_t outer_lo = 0;
  uint32_t inner_lo = 0;
  uint32_t width = 0;
  bool partial = false;
};

// The driver a link holds on one net set, where `partial`, to drive only
// `width` bits from `lo`, taking them from the bits from `src_lo` of what the
// other net resolved to.
void DriveOnly(ContAssignDriver& drv, bool partial, uint32_t lo,
               uint32_t src_lo, uint32_t width) {
  drv.partial = partial;
  drv.lo = lo;
  drv.src_lo = src_lo;
  drv.width = width;
}

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

  InoutPortLink(InoutPortLinkEnds e, LinkBits bits, Arena& arena)
      : ends(std::move(e)),
        toward_inner(ends.outer, arena),
        toward_outer(ends.inner, arena) {
    to_outer.net = &ends.outer;
    to_outer.origin = ends.inner_origin;
    to_outer.source_port = ends.port;
    to_inner.net = &ends.inner;
    to_inner.origin = ends.outer_origin;
    DriveOnly(to_outer, bits.partial, bits.outer_lo, bits.inner_lo, bits.width);
    DriveOnly(to_inner, bits.partial, bits.inner_lo, bits.outer_lo, bits.width);
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

// Joins the bits `bits` names of the two nets of `ends`, each direction told of
// every write to a driver of the net it carries from.
void RegisterLink(InoutPortLinkEnds ends, LinkBits bits, SimContext& ctx) {
  auto link =
      std::make_shared<InoutPortLink>(std::move(ends), bits, ctx.GetArena());
  link->ends.outer.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryIn(link, slot, ctx); });
  link->ends.inner.driver_listeners.emplace_back(
      [link, &ctx](std::size_t slot) { CarryOut(*link, slot, ctx); });
}

// One part of an inout port's connection: bits [lo, lo + width) of `net`,
// which the parent holds under `name`.
struct OuterPart {
  Net* net;
  std::string name;
  PartSelectBits bits;
};

// Appends the parts `e` names, the most significant first: each part of a
// concatenation in turn, and otherwise the net `e` names, all of it, or the
// bits a select of it names (§11.5.1). False where a part is no net of the
// parent.
bool CollectOuterParts(const Expr* e, const InoutPortConnection& conn,
                       SimContext& ctx, std::vector<OuterPart>& parts) {
  if (e->kind == ExprKind::kConcatenation) {
    return std::all_of(e->elements.begin(), e->elements.end(),
                       [&](const Expr* part) {
                         return CollectOuterParts(part, conn, ctx, parts);
                       });
  }
  const Expr* object = e;
  while (object->kind == ExprKind::kSelect) object = object->base;
  std::string name =
      GenBlockObjectKey(conn.outer_origin, conn.gen_blocks, object->text, ctx);
  Net* net = ctx.FindNet(name);
  if (net == nullptr) return false;
  PartSelectBits bits{0, net->resolved->value.width, 0};
  if (e != object)
    bits = SelectStorageBits(*net->resolved, e, ctx, ctx.GetArena());
  parts.push_back({net, std::move(name), bits});
  return true;
}

}  // namespace

void LinkInoutPortNets(InoutPortLinkEnds ends, SimContext& ctx) {
  // §23.3.3.7.1: an interconnect port's net is merged with the net connected
  // to it and so is of that net's type, which a join gives it by sharing the
  // net and two linked nets by the inner taking the outer's type.
  if (ends.inner.type == NetType::kInterconnect)
    ends.inner.type = ends.outer.type;
  RegisterLink(std::move(ends), LinkBits{}, ctx);
}

void LinkInoutPortConnection(const InoutPortConnection& conn, SimContext& ctx) {
  std::vector<OuterPart> parts;
  if (!CollectOuterParts(&conn.connection, conn, ctx, parts)) return;
  // §23.3.3 sizes a port connection like an assignment, so a connection
  // narrower than the port leaves the port's high bits unjoined and one wider
  // joins its low bits alone: each part takes the bits left above the parts
  // after it, as many of its own as fit.
  const int64_t kInnerWidth = conn.inner.resolved->value.width;
  uint32_t inner_lo = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    const auto kWidth = static_cast<uint32_t>(
        std::clamp<int64_t>(kInnerWidth - inner_lo, 0, it->bits.width));
    RegisterLink({*it->net, conn.inner, conn.outer_origin, conn.inner_origin,
                  conn.port, SdfHierName(it->name), SdfHierName(conn.port)},
                 {it->bits.lo, inner_lo, kWidth, true}, ctx);
    inner_lo += it->bits.width;
  }
}

std::string SdfHierName(const std::string& dotted) {
  std::string out = dotted;
  for (char& c : out) {
    if (c == '.') c = '/';
  }
  return out;
}

}  // namespace delta
