#pragma once

#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class Scheduler;
struct Variable;

/// Runtime net object for multi-driver resolution (IEEE 1800-2023 §6.5).
/// Each net has a resolved value, a net type determining the resolution
/// function, and a list of driver values.
struct DriverStrength {
  Strength s0 = Strength::kStrong;
  Strength s1 = Strength::kStrong;
};

// §28.12 R1: a net's strength is either a single unambiguous level or a range
// ("ambiguous strength consisting of more than one level"). A single-level
// side has hi == lo; a range-valued side has hi > lo. The two sides of the
// strength scale (value-0 and value-1 parts per §28.11 Figure 28-2) are
// tracked independently so that §28.12.2+ can record outcomes that span both.
struct NetStrength {
  Strength s0_hi = Strength::kHighz;
  Strength s0_lo = Strength::kHighz;
  Strength s1_hi = Strength::kHighz;
  Strength s1_lo = Strength::kHighz;

  bool IsAmbiguous() const { return s0_hi != s0_lo || s1_hi != s1_lo; }
};

struct Net {
  NetType type = NetType::kWire;
  Variable* resolved = nullptr;  // Points to the storage variable.
  std::vector<Logic4Vec> drivers;
  std::vector<DriverStrength> driver_strengths;
  NetStrength resolved_strength;

  // §6.6.4: Trireg charge strength and decay.
  Strength charge_strength = Strength::kMedium;
  Strength base_charge_strength =
      Strength::kMedium;  // §6.6.4.1: Declared strength.
  uint64_t decay_ticks = 0;
  uint64_t decay_generation = 0;

  // §6.6.7: User-defined nettype.
  bool is_user_nettype = false;
  std::string_view resolve_func;

  /// Resolve all driver values into the resolved variable.
  void Resolve(Arena& arena, Scheduler* sched = nullptr);

  /// Returns true if this is a trireg net with all drivers at Z.
  bool InCapacitiveState() const;
};

/// §6.6.4.1: Propagate charge between two connected trireg nets.
void PropagateCharge(Net& a, Net& b);

/// §6.6.4.1: Restore a net's charge strength to its declared value.
void DisconnectCharge(Net& net);

/// §28.12.2 R2: combine two ambiguous-strength net signals. The result's
/// per-side range includes every strength level in either input; in the
/// hi/lo encoding that is hi = max per side, lo = min per side.
NetStrength CombineAmbiguousStrength(NetStrength a, NetStrength b);

/// Resolve two Logic4Word values using wire/tri semantics (§28.7).
Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wand/triand semantics.
Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wor/trior semantics.
Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

}  // namespace delta
