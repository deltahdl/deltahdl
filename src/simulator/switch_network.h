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

void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches,
                               Arena& arena);

}
