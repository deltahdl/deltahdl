#pragma once

#include <cstdint>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// A net plus the variable that backs its resolved storage, sized to a given
// width. Used to exercise net.Resolve(arena) driver-resolution tests.
struct StrengthNet {
  Variable* var = nullptr;
  Net net;
};

// Builds a net of the given width whose resolved storage is a freshly created
// arena variable initialized to an all-x (default) 4-state vector. The net type
// defaults to kWire; pass a different NetType for tri/wand/etc. variants.
inline StrengthNet MakeStrengthNet(Arena& arena, uint32_t width,
                                   NetType type = NetType::kWire) {
  StrengthNet sn;
  sn.var = arena.Create<Variable>();
  sn.var->value = MakeLogic4Vec(arena, width);
  sn.net.type = type;
  sn.net.resolved = sn.var;
  return sn;
}

// Appends one driver to a net: a value vector of the given width and a uniform
// driver strength applied to both the 0 and 1 sides.
inline void AddDriver(Arena& arena, Net& net, uint32_t width, uint64_t value,
                      Strength strength) {
  net.drivers.push_back(MakeLogic4VecVal(arena, width, value));
  net.driver_strengths.push_back({strength, strength});
}
