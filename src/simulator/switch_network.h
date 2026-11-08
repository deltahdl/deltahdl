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

struct BidirSwitchDelaySpec {
  bool has_turn_on = false;
  bool has_turn_off = false;
  uint64_t turn_on = 0;
  uint64_t turn_off = 0;
};

uint64_t BidirSwitchTurnOnDelay(const BidirSwitchDelaySpec& spec);

uint64_t BidirSwitchTurnOffDelay(const BidirSwitchDelaySpec& spec);

uint64_t BidirSwitchBuiltinControlXZDelay(const BidirSwitchDelaySpec& spec);

void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches,
                               Arena& arena);

struct BidirSwitchState {
  static constexpr uint8_t kOff = 0;
  static constexpr uint8_t kOn = 1;
  static constexpr uint8_t kUnknown = 2;
  BidirSwitchKind kind = BidirSwitchKind::kTran;
  uint8_t state = kOff;
  bool user_defined_nets = false;
  bool is_alias = false;
};

uint8_t BidirSwitchStateFor(BidirSwitchKind kind, Logic4Word control);

bool ResolveSwitchGroup(Net& net, Arena& arena, Scheduler* sched);

}  // namespace delta
