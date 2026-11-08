#pragma once

#include <cstdint>

#include "parser/ast_module.h"

namespace delta {

enum class GateType : uint8_t {
  kCmosSwitch,
  kEnableGate,
  kMosSwitch,
  kNInputGate,
  kNOutputGate,
  kPassEnSwitch,
  kPassSwitch,
  kPullGate,
};

inline GateType GateTypeOf(GateKind kind) {
  switch (kind) {
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
      return GateType::kNInputGate;
    case GateKind::kBuf:
    case GateKind::kNot:
      return GateType::kNOutputGate;
    case GateKind::kBufif0:
    case GateKind::kBufif1:
    case GateKind::kNotif0:
    case GateKind::kNotif1:
      return GateType::kEnableGate;
    case GateKind::kTran:
    case GateKind::kRtran:
      return GateType::kPassSwitch;
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      return GateType::kPassEnSwitch;
    case GateKind::kNmos:
    case GateKind::kPmos:
    case GateKind::kRnmos:
    case GateKind::kRpmos:
      return GateType::kMosSwitch;
    case GateKind::kCmos:
    case GateKind::kRcmos:
      return GateType::kCmosSwitch;
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return GateType::kPullGate;
  }
  return GateType::kPullGate;
}

}  // namespace delta
