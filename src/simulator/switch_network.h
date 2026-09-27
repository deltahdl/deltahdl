#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class Scheduler;
struct Net;
struct Variable;

enum class BidirSwitchKind : uint8_t {
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
};

struct BidirSwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  BidirSwitchKind kind = BidirSwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
};

bool BidirSwitchConducts(BidirSwitchKind kind, Logic4Word control);

bool BidirSwitchControlIsUnknown(BidirSwitchKind kind, Logic4Word control);

// §28.8: A pass-enable bidirectional switch (tranif0/tranif1/rtranif0/rtranif1)
// may carry a delay specification of one or two values that constrains only the
// control input; the bidirectional data path itself has no propagation delay.
// The two slots hold the turn-on and turn-off values when present, so the
// selection helpers below can apply the 0/1/2-delay rules without re-deriving
// the spec's shape.
struct BidirSwitchDelaySpec {
  bool has_turn_on = false;
  bool has_turn_off = false;
  uint64_t turn_on = 0;
  uint64_t turn_off = 0;
};

// §28.8: With two delays the first value drives the control-input turn-on
// transition; with one delay that single value applies to both edges; with no
// delay there is no turn-on delay.
uint64_t BidirSwitchTurnOnDelay(const BidirSwitchDelaySpec& spec);

// §28.8: Mirror of the turn-on rule — the second delay drives turn-off when
// present, otherwise a lone delay applies to both edges and absence means none.
uint64_t BidirSwitchTurnOffDelay(const BidirSwitchDelaySpec& spec);

// §28.8: For bidirectional switches connecting built-in net types, control
// transitions to x and z take the smaller of the two delays; a single delay or
// no delay collapses to that value.
uint64_t BidirSwitchBuiltinControlXZDelay(const BidirSwitchDelaySpec& spec);

void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches,
                               Arena& arena);

// §28.8: one bidirectional switch as a run holds it, which the nets at its two
// terminals link to (Net::switch_links). `state` is kOff, kOn, or kUnknown
// where a tranif0, tranif1, rtranif0 or rtranif1 has a control of x or z; a
// tran or rtran is on for as long as the run lasts.
struct BidirSwitchState {
  static constexpr uint8_t kOff = 0;
  static constexpr uint8_t kOn = 1;
  static constexpr uint8_t kUnknown = 2;
  BidirSwitchKind kind = BidirSwitchKind::kTran;
  uint8_t state = kOff;
  bool user_defined_nets = false;
};

// The state a control value puts a switch of `kind` in.
uint8_t BidirSwitchStateFor(BidirSwitchKind kind, Logic4Word control);

// §28.8: resolves every net joined to `net` through bidirectional switches,
// each from its own drivers and from the drivers of the nets it reaches
// through switches that conduct. Answers false, resolving nothing, where
// `net` is being resolved as one of such a group already, for the caller to
// resolve it from the drivers it has.
bool ResolveSwitchGroup(Net& net, Arena& arena, Scheduler* sched);

}  // namespace delta
