#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/contassign_delay.h"

namespace delta {

class Arena;
class Scheduler;
struct Variable;

struct DriverStrength {
  Strength s0 = Strength::kStrong;
  Strength s1 = Strength::kStrong;
  // §28.12.2: the lower end of the range a driven 0 (s0_lo) or 1 (s1_lo) spans
  // where the driver passes on an ambiguous strength, as a MOS switch passes
  // its data input's (§28.13, §28.14): a 1 from pull to strong has s1 strong
  // and s1_lo pull. High impedance where the value is driven at its one level,
  // which a known value's range never reaches down to; an x's range is given
  // by its two levels alone.
  Strength s0_lo = Strength::kHighz;
  Strength s1_lo = Strength::kHighz;
};

struct Net;
struct BidirSwitchState;

// §28.8: one bidirectional pass switch a net is a terminal of -- the net at
// its other terminal, and the switch, whose state says whether it conducts.
struct SwitchLink {
  Net* other = nullptr;
  const BidirSwitchState* sw = nullptr;
  // §10.11: where the link joins bits of the two nets rather than the nets
  // whole, the pairs it joins -- a bit of this net, then the bit of `other`
  // it is one with, each counted from the least significant end. Null for a
  // switch, which joins its terminals whole.
  const std::vector<std::pair<uint32_t, uint32_t>>* bit_map = nullptr;
};

struct NetStrength {
  Strength s0_hi = Strength::kHighz;
  Strength s0_lo = Strength::kHighz;
  Strength s1_hi = Strength::kHighz;
  Strength s1_lo = Strength::kHighz;

  bool IsAmbiguous() const { return s0_hi != s0_lo || s1_hi != s1_lo; }
};

struct Net {
  NetType type = NetType::kWire;
  Variable* resolved = nullptr;
  std::vector<Logic4Vec> drivers;
  std::vector<DriverStrength> driver_strengths;
  // §21.7.4.3.2: the hierarchical prefix of the instance each driver stands
  // in, slot for slot with `drivers` where a continuous assignment recorded
  // one (ApplyContAssignToNet), so a dumped inout port can tell its input end,
  // the drivers outside its instance, from its output end, those inside. A
  // slot past the end, or one no assignment filled, records no instance.
  std::vector<std::string_view> driver_origins;
  // §32.4.4: the module output port each driver stands for, where an
  // instance's output port connection drives the net, slot for slot with
  // `drivers`; empty for a driver of any other kind. An interconnect delay is
  // annotated from such a port.
  std::vector<std::string_view> driver_ports;
  // §32.4.4: told the slot of every driver whose value a continuous
  // assignment writes, which is how a load annotated with a delay of its own
  // from each source sees which source moved.
  std::vector<std::function<void(std::size_t)>> driver_listeners;
  NetStrength resolved_strength;

  // §21.2.1.4: the strength of each bit of this net, indexed from the least
  // significant end of its storage. A net reports one strength, which is what
  // resolved_strength holds: the resolutions that can answer differently for
  // different bits compute a strength per bit and widen the bits into that one
  // pair. A bit-select of a vector net names one of those bits, and the scalar
  // whose strength §21.2.1.4 reports is the bit rather than the net, so the
  // per-bit answers are kept as well as folded.
  //
  // Empty wherever no resolution filled it: a supply net and a tri0/tri1
  // default give every bit of the net one strength by construction, and the
  // remaining paths compute no strength at all. BitStrength answers from
  // resolved_strength there, which is that bit's own answer in the first two
  // cases and the same thing the net reports in the rest.
  std::vector<NetStrength> bit_strengths;

  Strength charge_strength = Strength::kMedium;
  Strength base_charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
  // §28.16.2.1: whether this net decays, which decay_ticks alone cannot say.
  // See RtlirNet::decays in src/elaborator/rtlir.h.
  bool decays = false;
  // §28.15.2 and §28.16.2: for each bit of a trireg, the tick it entered the
  // charge storage state at -- a source drove it and then went to high
  // impedance -- or that a source drives it, or that it holds the x the net
  // starts with, which no driver left and which stands against no source.
  // SettleTriregCharge (simulator/net_trireg.h) keeps it; empty until the net
  // first resolves.
  std::vector<uint64_t> charge_since;

  bool is_user_nettype = false;
  std::string_view resolve_func;
  // §6.6.7: the call of the resolution function, for the net's drivers
  // (AttachNettypeResolution in nettype_resolution.cpp); empty where the
  // nettype declares none.
  std::function<Logic4Vec(const std::vector<Logic4Vec>&, Arena&)> resolve_hook;

  // §28.8: the bidirectional switches this net is a terminal of, and the
  // drivers of the nets they join it to, which it resolves with its own. The
  // latter are gathered by ResolveSwitchGroup (simulator/switch_network.h)
  // each time the group resolves, their strengths already reduced across the
  // switches as §28.13 and §28.14 say.
  std::vector<SwitchLink> switch_links;
  std::vector<Logic4Vec> switch_drivers;
  std::vector<DriverStrength> switch_strengths;

  void Resolve(Arena& arena, Scheduler* sched = nullptr);

  // §21.2.1.4: the strength of the bit sitting `bit` places above the least
  // significant end of this net, which is the scalar a bit-select of a vector
  // net names. Falls back to the strength the net as a whole reports where no
  // resolution recorded the bits separately.
  NetStrength BitStrength(uint32_t bit) const;

  bool InCapacitiveState() const;

  // §28.16: the net delay the net was declared with, and the change it holds
  // back: the value its sources last resolved to that has not yet landed, with
  // that value's strengths, and a count that tells a pending change from one
  // a later resolution replaced (§10.3.3's descheduling).
  std::optional<ContAssignDelays> delay;
  std::optional<Logic4Vec> pending_value;
  uint64_t delay_generation = 0;

  // Whether a MOS or CMOS switch reads the net as its data input, which makes
  // Resolve record a change of the net's strength
  // (Variable::strength_generation) for the switch to pass on (§28.13, §28.14).
  bool strength_watched = false;
};

void PropagateCharge(Net& a, Net& b);

void DisconnectCharge(Net& net);

NetStrength CombineAmbiguousStrength(NetStrength a, NetStrength b);

// §28.12.3: combines a signal of known value and unambiguous strength with a
// signal of ambiguous strength. `vu` is the unambiguous signal's value, 0 or 1,
// and `su` the strength level it drives at. On the side of the opposite value
// the ambiguous levels above `su` remain (rule a), those at or below it
// disappear (rule b), and the gap those two rules open between `su` and the
// lowest surviving level is filled back in, because the two signals are of
// opposite value (rule c). The gap is filled only where `su` is itself in the
// result: §28.12.1 has an ambiguous signal every one of whose levels is
// stronger than `su` dominate the unambiguous signal outright, and a gap needs
// that level to bound it from below. On the side of `vu` the signals agree, so
// each ambiguous level resolves against `su` to whichever of the two is
// stronger.
//
// The clause combines the ambiguous signal with one signal of known value and
// unambiguous strength, so a net carrying several such signals weaker than its
// ambiguous signal has one combination to make per signal: apply this to the
// result of the last, once for each of them.
NetStrength CombineAmbigWithUnambig(NetStrength ambig, uint8_t vu, uint8_t su);

enum class WiredLogicKind : uint8_t { kAnd, kOr };

// Pairwise per LRM §28.12.4: the per-side max/min shortcut used for
// non-wired-logic ambiguous combinations does not commute with wired AND/OR.
NetStrength CombineWiredLogicAmbiguous(NetStrength a, NetStrength b,
                                       WiredLogicKind kind);

Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

// §6.6.7 user-defined nettypes. A nettype names a data type and, optionally, a
// resolution function. The classification of admissible data types and the
// driver-resolution behavior are exposed as pure helpers so the normative rules
// can be applied and observed independently of the surrounding driver-update
// machinery.

// The data-type categories a user-defined nettype declaration can name. The
// first five are the categories §6.6.7 admits; the remainder are representative
// categories it excludes.
enum class NettypeDataKind : uint8_t {
  k4StateIntegral,
  k2StateIntegral,
  kReal,
  kShortreal,
  kFixedUnpackedArray,
  kDynamicArray,
  kString,
  kClass,
};

// A resolution function maps the set of current driver values onto the single
// resolved value of an atomic net.
using ResolutionFn =
    std::function<Logic4Vec(Arena&, const std::vector<Logic4Vec>&)>;

struct UserNettype {
  NettypeDataKind data_kind = NettypeDataKind::k4StateIntegral;
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

// §6.6.7: a valid data type for a user-defined nettype shall be a 4-state or
// 2-state integral type, a real or shortreal, or a fixed-size unpacked
// aggregate whose elements are themselves valid. Returns false for the
// categories the clause excludes (dynamic arrays, strings, class handles).
bool ValidateNettypeDataKind(NettypeDataKind kind);

// §6.6.7: when a resolution function is specified, a change in any driver makes
// the simulator recompute the net's value from all of its drivers as a whole --
// the net is an atomic net. Writes the resolved value back into the net.
bool ResolveUserDefinedNet(Net& net, const UserNettype& nettype, Arena& arena);

// §6.6.7: a nettype declared without a resolution function makes it an error
// for a net of that nettype to be driven by more than one driver.
bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt);

// §6.7.3 initialization of nets with user-defined nettypes. The rules below all
// describe the state a nettype net is brought to at time zero, before any
// initial/always procedure runs, so they are exposed as a pure helper that can
// be applied and observed without the surrounding scheduling machinery.

// §6.7.3: establish a nettype net's value at time zero. First the net's initial
// value is set to the default defined by its data type (per Table 6-7); for a
// 4-state data type that default is x, not z. The resolution function, when the
// nettype has one, is then activated exactly once -- this guaranteed call
// happens even when the net has no drivers, in which case it is handed an empty
// driver array. Returns false only when the net has no resolved storage.
bool InitializeUserDefinedNet(Net& net, const UserNettype& nettype,
                              Arena& arena);

// §6.7.3: one initializer for a member of a struct-typed nettype net. offset is
// the member's least-significant bit position within the packed struct value.
struct StructMemberInit {
  uint32_t offset = 0;
  uint32_t width = 0;
  bool has_initializer = false;
  Logic4Vec init_value;
};

// §6.7.3: compute the time-zero value of a net whose nettype data type is a
// struct. Members start at the 4-state data-type default (x); any member that
// carries an initialization expression has that value applied over its bits.
Logic4Vec InitialStructNetValue(Arena& arena, uint32_t total_width,
                                const std::vector<StructMemberInit>& members);

}  // namespace delta
