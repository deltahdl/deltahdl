#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
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

}  // namespace delta
