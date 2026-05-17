#pragma once

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

Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

}
