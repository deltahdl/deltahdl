#pragma once

#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
struct Variable;

/// Runtime net object for multi-driver resolution (IEEE 1800-2023 §6.5).
/// Each net has a resolved value, a net type determining the resolution
/// function, and a list of driver values.
struct Net {
  NetType type = NetType::kWire;
  Variable* resolved = nullptr;  // Points to the storage variable.
  std::vector<Logic4Vec> drivers;

  /// Resolve all driver values into the resolved variable.
  void Resolve(Arena& arena);
};

/// Resolve two Logic4Word values using wire/tri semantics (§28.7).
Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wand/triand semantics.
Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

/// Resolve two Logic4Word values using wor/trior semantics.
Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

}  // namespace delta
