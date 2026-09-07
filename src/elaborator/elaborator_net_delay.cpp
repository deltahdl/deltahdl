#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast.h"

// §28.16's net delay and §10.3.3's rule for adding it to the drivers of the net
// it was declared on. The delay a driver writes and the delay its net writes
// are two consecutive segments of one path -- the driver's from its inputs to
// its output, the net's from that output changing to the net updating -- so a
// driver carrying its own delay is given the sum, and one carrying none is
// given the net's. Adding them means writing §28.16's one- and two-delay
// defaults out as expressions first, which is the whole of what this file does
// beyond the walk.

namespace delta {

// §28.16: the nets of `mod` that carry a net delay, keyed by their names, which
// is what a driver of one names it by.
static std::unordered_map<std::string_view, const RtlirNet*> CollectDelayedNets(
    const RtlirModule* mod) {
  std::unordered_map<std::string_view, const RtlirNet*> delayed;
  for (const RtlirNet& net : mod->nets) {
    if (net.delay_rise == nullptr) continue;
    delayed.emplace(net.name, &net);
  }
  return delayed;
}

// The net of `delayed` that `lhs` drives, or null where `lhs` drives none of
// them. A left-hand side naming no single signal reaches no entry, because
// LhsSignalName answers an empty name for it and no net is declared under one.
static const RtlirNet* FindDelayedNetDriven(
    const Expr* lhs,
    const std::unordered_map<std::string_view, const RtlirNet*>& delayed) {
  auto it = delayed.find(LhsSignalName(lhs));
  if (it == delayed.end()) return nullptr;
  return it->second;
}

// One delay specification's three slots, each an expression, with §28.16's
// defaults expanded so that two specifications can be added slot by slot.
struct DelayTriple {
  Expr* rise = nullptr;
  Expr* fall = nullptr;
  Expr* decay = nullptr;
};

static Expr* MakeBinaryExpr(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* bin = arena.Create<Expr>();
  bin->kind = ExprKind::kBinary;
  bin->op = op;
  bin->lhs = lhs;
  bin->rhs = rhs;
  return bin;
}

// §28.16: "The delay when the signal changes to high impedance or to unknown
// shall be the lesser of the two delay values." No Expr spells a minimum, so it
// is written as the conditional that computes one, which is what the clause
// says in the vocabulary the tree has.
static Expr* MakeLesserOf(Arena& arena, Expr* a, Expr* b) {
  auto* cond = MakeBinaryExpr(arena, TokenKind::kLt, a, b);
  auto* tern = arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = cond;
  tern->true_expr = a;
  tern->false_expr = b;
  return tern;
}

// §28.16's defaults written out. "For both gates and nets, the default delay
// shall be zero when no delay specification is given. When one delay value is
// given, then this value shall be used for all propagation delays associated
// with the gate or the net. When two delays are given, the first delay shall
// specify the rise delay, and the second delay shall specify the fall delay.
// The delay when the signal changes to high impedance or to unknown shall be
// the lesser of the two delay values."
//
// A specification is expanded before it is added to another, because the slots
// a source left unwritten are not zero: a `#2` against a `#(5,7)` has a fall
// delay of 2 to add to 7, and reading its null fall slot as nothing would add
// the net's alone.
static DelayTriple ExpandDelaySpec(Arena& arena, Expr* rise, Expr* fall,
                                   Expr* decay) {
  DelayTriple t;
  if (rise == nullptr) return t;
  t.rise = rise;
  if (fall == nullptr) {
    t.fall = rise;
    t.decay = rise;
    return t;
  }
  t.fall = fall;
  t.decay = decay != nullptr ? decay : MakeLesserOf(arena, rise, fall);
  return t;
}

// §10.3.3: a net delay is added to the delay of the drivers on the net. The
// clause states it as the exception a declaration assignment is: "the delay is
// part of the continuous assignment and is not a net delay. Thus, it shall not
// be added to the delay of other drivers on the net" -- a "thus" that follows
// only where a delay that is a net delay is added to them. §28.16 gives the two
// consecutive segments of one path, the driver's from its inputs to its output
// and the net's from that output changing to the net updating, so the time from
// one to the other is their sum.
static void AddNetDelayToDriverDelay(Arena& arena, RtlirContAssign& ca,
                                     const RtlirNet& net) {
  DelayTriple driver =
      ExpandDelaySpec(arena, ca.delay, ca.delay_fall, ca.delay_decay);
  DelayTriple net_delay =
      ExpandDelaySpec(arena, net.delay_rise, net.delay_fall, net.delay_turnoff);
  if (driver.rise == nullptr || net_delay.rise == nullptr) return;
  ca.delay =
      MakeBinaryExpr(arena, TokenKind::kPlus, driver.rise, net_delay.rise);
  ca.delay_fall =
      MakeBinaryExpr(arena, TokenKind::kPlus, driver.fall, net_delay.fall);
  ca.delay_decay =
      MakeBinaryExpr(arena, TokenKind::kPlus, driver.decay, net_delay.decay);
}

// §29.2 makes a primitive instance's output terminal a driver on the net
// connected to it, and §28.16 gives a net delay to "any driver on the net", so
// an instance drives its net through the same two segments a gate or a
// continuous assignment does. A gate reaches the walk above because
// elaborator_gates.cpp lowers it to an RtlirContAssign; §29.8's instances stand
// in RtlirModule::udp_insts instead and reached it through nothing, so the same
// net was delayed for one driver and not for the other.
//
// §29.8 gives an instance two delay slots and no third -- "Only two delays may
// be specified because z is not supported for UDPs" -- so the sum is written
// into those two and the net's turn-off delay has nowhere to go, which is right
// for a driver that never goes to z.
static void ApplyNetDelaysToUdpInstances(
    Arena& arena, RtlirModule* mod,
    const std::unordered_map<std::string_view, const RtlirNet*>& delayed) {
  for (RtlirUdpInst& inst : mod->udp_insts) {
    const RtlirNet* net = FindDelayedNetDriven(inst.output, delayed);
    if (net == nullptr) continue;
    if (inst.delay == nullptr) {
      inst.delay = net->delay_rise;
      inst.delay_fall = net->delay_fall;
      continue;
    }
    DelayTriple own =
        ExpandDelaySpec(arena, inst.delay, inst.delay_fall, nullptr);
    DelayTriple net_delay = ExpandDelaySpec(
        arena, net->delay_rise, net->delay_fall, net->delay_turnoff);
    if (net_delay.rise == nullptr) continue;
    inst.delay =
        MakeBinaryExpr(arena, TokenKind::kPlus, own.rise, net_delay.rise);
    inst.delay_fall =
        MakeBinaryExpr(arena, TokenKind::kPlus, own.fall, net_delay.fall);
  }
}

void ApplyNetDeclDelaysToDrivers(Arena& arena, RtlirModule* mod) {
  std::unordered_map<std::string_view, const RtlirNet*> delayed =
      CollectDelayedNets(mod);
  for (RtlirContAssign& ca : mod->assigns) {
    const RtlirNet* net = FindDelayedNetDriven(ca.lhs, delayed);
    if (net == nullptr) continue;
    // A driver that wrote a delay of its own has the net's added to it, which
    // is what §10.3.3 states of a net delay. A driver that wrote none takes the
    // net's slots as they stand: there is nothing to add them to, and copying
    // the expressions rather than expanding them leaves a one-delay
    // specification the one slot it was written with, which is what every
    // reader of these fields already handles.
    if (ca.delay != nullptr) {
      AddNetDelayToDriverDelay(arena, ca, *net);
      continue;
    }
    ca.delay = net->delay_rise;
    ca.delay_fall = net->delay_fall;
    ca.delay_decay = net->delay_turnoff;
  }
  ApplyNetDelaysToUdpInstances(arena, mod, delayed);
}

}  // namespace delta
