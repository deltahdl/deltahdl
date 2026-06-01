#pragma once

#include <cstdint>
#include <functional>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class Scheduler;
struct Variable;

struct DriverStrength {
  Strength s0 = Strength::kStrong;
  Strength s1 = Strength::kStrong;
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
  NetStrength resolved_strength;

  Strength charge_strength = Strength::kMedium;
  Strength base_charge_strength =
      Strength::kMedium;
  uint64_t decay_ticks = 0;
  uint64_t decay_generation = 0;

  bool is_user_nettype = false;
  std::string_view resolve_func;

  void Resolve(Arena& arena, Scheduler* sched = nullptr);

  bool InCapacitiveState() const;
};

void PropagateCharge(Net& a, Net& b);

void DisconnectCharge(Net& net);

NetStrength CombineAmbiguousStrength(NetStrength a, NetStrength b);

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

// §6.6.7: a nettype declared without a resolution function makes it an error for
// a net of that nettype to be driven by more than one driver.
bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt);

}
