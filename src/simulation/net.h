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

struct Net {
  NetType type = NetType::kWire;
  Variable* resolved = nullptr;  // Points to the storage variable.
  std::vector<Logic4Vec> drivers;
  std::vector<DriverStrength> driver_strengths;

  // §6.6.4: Trireg charge strength and decay.
  Strength charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
  uint64_t decay_generation = 0;

  /// Resolve all driver values into the resolved variable.
  void Resolve(Arena& arena, Scheduler* sched = nullptr);

  /// Returns true if this is a trireg net with all drivers at Z.
  bool InCapacitiveState() const;
};

/// §6.6.4.1: Propagate charge between two connected trireg nets.
void PropagateCharge(Net& a, Net& b);

/// Resolve two Logic4Word values using wire/tri semantics (§28.7).
Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wand/triand semantics.
Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wor/trior semantics.
Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

}  // namespace delta
