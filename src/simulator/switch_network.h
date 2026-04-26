#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
struct Net;
struct Variable;

// §4.9.5: Bidirectional switch (transistor) kinds. The source elements that
// model switches per IEEE 1800-2023 are tran, tranif0, tranif1, rtran,
// rtranif0, and rtranif1.
enum class BidirSwitchKind : uint8_t {
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
};

// §4.9.5: Runtime record of one bidirectional switch device. terminal_a and
// terminal_b are the two switch-connected nets. user_defined_nets selects the
// user-defined-net rule for x/z control inputs (§4.9.5 paragraph 6).
struct BidirSwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  BidirSwitchKind kind = BidirSwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
};

// True when the gate is on for the given control value. tran/rtran always
// conduct; the if-variants gate on the control's known 0/1 polarity.
bool BidirSwitchConducts(BidirSwitchKind kind, Logic4Word control);

// True when the if-variant control input is x or z. tran/rtran have no
// control input and always return false.
bool BidirSwitchControlIsUnknown(BidirSwitchKind kind, Logic4Word control);

// §4.9.5: Resolve a switch-connected network as a whole rather than one
// device at a time. The pass:
//   1. Initialises each terminal from its driver value so subsequent steps
//      see a consistent starting point.
//   2. Applies the §4.9.5 rule for built-in nets when the control input is
//      x: the steady-state response equals the unique level common to the
//      fully-conducting and nonconducting solutions, otherwise x.
//   3. For user-defined nets the switch is treated as off when the control
//      is x or z, leaving the two terminal nets resolved separately.
//   4. Propagates a known driven value across cascaded conducting switches
//      so a single source reaches every undriven node it can reach.
void ResolveBidirSwitchNetwork(std::vector<BidirSwitchInst>& switches,
                               Arena& arena);

}  // namespace delta
