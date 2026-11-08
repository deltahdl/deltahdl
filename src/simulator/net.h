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
  Strength s0_lo = Strength::kHighz;
  Strength s1_lo = Strength::kHighz;
};

struct Net;
struct BidirSwitchState;

struct SwitchLink {
  Net* other = nullptr;
  const BidirSwitchState* sw = nullptr;
  const std::vector<std::pair<uint32_t, uint32_t>>* bit_map = nullptr;
};

struct NetStrength {
  Strength s0_hi = Strength::kHighz;
  Strength s0_lo = Strength::kHighz;
  Strength s1_hi = Strength::kHighz;
  Strength s1_lo = Strength::kHighz;

  bool IsAmbiguous() const { return s0_hi != s0_lo || s1_hi != s1_lo; }
  bool operator==(const NetStrength&) const = default;
};

struct Net {
  NetType type = NetType::kWire;
  Variable* resolved = nullptr;
  std::vector<Logic4Vec> drivers;
  std::vector<DriverStrength> driver_strengths;
  std::vector<std::string_view> driver_origins;
  std::vector<std::string_view> driver_ports;
  std::vector<std::function<void(std::size_t)>> driver_listeners;
  NetStrength resolved_strength;

  std::vector<NetStrength> bit_strengths;

  Strength charge_strength = Strength::kMedium;
  Strength base_charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
  bool decays = false;
  std::vector<uint64_t> charge_since;

  bool is_user_nettype = false;
  std::string_view resolve_func;
  std::function<Logic4Vec(const std::vector<Logic4Vec>&, Arena&)> resolve_hook;

  std::vector<SwitchLink> switch_links;
  std::vector<Logic4Vec> switch_drivers;
  std::vector<DriverStrength> switch_strengths;

  void Resolve(Arena& arena, Scheduler* sched = nullptr);

  NetStrength BitStrength(uint32_t bit) const;

  bool InCapacitiveState() const;

  std::optional<ContAssignDelays> delay;
  std::optional<Logic4Vec> pending_value;
  uint64_t delay_generation = 0;
  std::optional<Logic4Vec> pending_path_value;

  bool strength_watched = false;
};

void PropagateCharge(Net& a, Net& b);

void DisconnectCharge(Net& net);

NetStrength CombineAmbiguousStrength(NetStrength a, NetStrength b);

NetStrength CombineAmbigWithUnambig(NetStrength ambig, uint8_t vu, uint8_t su);

enum class WiredLogicKind : uint8_t { kAnd, kOr };

NetStrength CombineWiredLogicAmbiguous(NetStrength a, NetStrength b,
                                       WiredLogicKind kind);

Logic4Word ResolveWireWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWandWord(Logic4Word a, Logic4Word b);

Logic4Word ResolveWorWord(Logic4Word a, Logic4Word b);

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

using ResolutionFn =
    std::function<Logic4Vec(Arena&, const std::vector<Logic4Vec>&)>;

struct UserNettype {
  NettypeDataKind data_kind = NettypeDataKind::k4StateIntegral;
  uint32_t bit_width = 1;
  ResolutionFn resolution;
};

bool ValidateNettypeDataKind(NettypeDataKind kind);

bool ResolveUserDefinedNet(Net& net, const UserNettype& nettype, Arena& arena);

bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt);

bool InitializeUserDefinedNet(Net& net, const UserNettype& nettype,
                              Arena& arena);

struct StructMemberInit {
  uint32_t offset = 0;
  uint32_t width = 0;
  bool has_initializer = false;
  Logic4Vec init_value;
};

Logic4Vec InitialStructNetValue(Arena& arena, uint32_t total_width,
                                const std::vector<StructMemberInit>& members);

}  // namespace delta
