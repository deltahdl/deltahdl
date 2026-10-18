#pragma once

#include <cstdint>

#include "parser/ast_module.h"

namespace delta {

// The type A.3.4 gives a gate or switch keyword, which is what A.3.1's
// instance productions are written against: cmos_switchtype is `cmos | rcmos`,
// enable_gatetype `bufif0 | bufif1 | notif0 | notif1`, mos_switchtype `nmos |
// pmos | rnmos | rpmos`, n_input_gatetype `and | nand | or | nor | xor |
// xnor`, n_output_gatetype `buf | not`, pass_en_switchtype `tranif0 | tranif1
// | rtranif1 | rtranif0` and pass_switchtype `tran | rtran`. The pull gate is
// A.3.1's own, `pullup` and `pulldown` opening pull_gate_instance with no type
// production of their own, and stands here as the eighth so that every
// GateKind has a type.
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

// The A.3.4 type of a gate kind. Written once, here, for the reason
// IsProceduralItemKind is written beside ModuleItemKind in ast_module.h: what
// A.3.1 lets an instance carry -- a drive_strength, a delay2 or a delay3, and
// how many terminals -- is given per type, and a caller that spells a type's
// kinds out for itself is one more list to keep whole. A kind added to
// GateKind is added to its type here.
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
