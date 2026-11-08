#pragma once

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

struct StrengthNet {
  Variable* var = nullptr;
  Net net;
};

inline StrengthNet MakeStrengthNet(Arena& arena, uint32_t width,
                                   NetType type = NetType::kWire) {
  StrengthNet sn;
  sn.var = arena.Create<Variable>();
  sn.var->value = MakeLogic4Vec(arena, width);
  sn.net.type = type;
  sn.net.resolved = sn.var;
  return sn;
}

inline void AddDriver(Arena& arena, Net& net, uint32_t width, uint64_t value,
                      Strength strength) {
  net.drivers.push_back(MakeLogic4VecVal(arena, width, value));
  net.driver_strengths.push_back({strength, strength});
}
