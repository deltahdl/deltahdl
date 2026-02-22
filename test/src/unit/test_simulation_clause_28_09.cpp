// §28.9: CMOS switches

#include <gtest/gtest.h>
#include <cstdint>

// --- Local types for MOS/pass switches (§28.7, §28.8, §28.9) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

enum class Val4Ext : uint8_t {
  kV0 = 0,
  kV1 = 1,
  kX = 2,
  kZ = 3,
  kL = 4,
  kH = 5
};

enum class SwitchType : uint8_t {
  kNmos,
  kPmos,
  kRnmos,
  kRpmos,
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
  kCmos,
  kRcmos,
};

Val4Ext EvalMosSwitch(SwitchType type, Val4 data, Val4 control);

bool IsBidirectional(SwitchType type);

bool AcceptsDelaySpec(SwitchType type);

uint32_t MaxSwitchDelays(SwitchType type);

// --- Implementations ---
Val4Ext EvalMosSwitch(SwitchType type, Val4 data, Val4 control) {
  // §28.7 Table 28-6: z data always produces z regardless of control.
  if (data == Val4::kZ) return Val4Ext::kZ;

  // Determine the effective control for NMOS-like behavior.
  // NMOS/RNMOS: conducts when control=1.
  // PMOS/RPMOS: conducts when control=0 (complementary).
  // CMOS/RCMOS: treated as NMOS+PMOS; control input = ncontrol, conducts
  //   when ncontrol=1.
  bool complementary =
      (type == SwitchType::kPmos || type == SwitchType::kRpmos);

  Val4 eff = control;
  if (complementary) {
    // Invert the control signal for PMOS-like switches.
    switch (control) {
      case Val4::kV0:
        eff = Val4::kV1;
        break;
      case Val4::kV1:
        eff = Val4::kV0;
        break;
      default:
        eff = control;
        break;  // x/z stay as-is
    }
  }

  // Now evaluate with NMOS semantics: conducts when eff=1, blocks when eff=0.
  switch (eff) {
    case Val4::kV1:
      // Conducting: data passes through.
      switch (data) {
        case Val4::kV0:
          return Val4Ext::kV0;
        case Val4::kV1:
          return Val4Ext::kV1;
        case Val4::kX:
          return Val4Ext::kX;
        case Val4::kZ:
          return Val4Ext::kZ;
      }
      break;
    case Val4::kV0:
      // Blocked: output is z.
      return Val4Ext::kZ;
    case Val4::kX:
    case Val4::kZ:
      // Unknown control: weaken the output.
      switch (data) {
        case Val4::kV0:
          return Val4Ext::kL;
        case Val4::kV1:
          return Val4Ext::kH;
        case Val4::kX:
          return Val4Ext::kX;
        case Val4::kZ:
          return Val4Ext::kZ;
      }
      break;
  }
  return Val4Ext::kX;  // Unreachable.
}

bool IsBidirectional(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
    case SwitchType::kTranif0:
    case SwitchType::kTranif1:
    case SwitchType::kRtranif0:
    case SwitchType::kRtranif1:
      return true;
    default:
      return false;
  }
}

bool AcceptsDelaySpec(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
      return false;
    default:
      return true;
  }
}

uint32_t MaxSwitchDelays(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
      return 0;
    case SwitchType::kTranif0:
    case SwitchType::kTranif1:
    case SwitchType::kRtranif0:
    case SwitchType::kRtranif1:
      return 2;
    case SwitchType::kNmos:
    case SwitchType::kPmos:
    case SwitchType::kRnmos:
    case SwitchType::kRpmos:
    case SwitchType::kCmos:
    case SwitchType::kRcmos:
      return 3;
  }
  return 0;  // Unreachable.
}

namespace {

// §28.8: "These devices shall have no propagation delay through the
//  bidirectional terminals."
// §28.8: "tranif0, tranif1 ... when turned off, they shall block
//  signals; and when they are turned on, they shall pass signals."
// =============================================================
// §28.9: CMOS switches
// =============================================================
// §28.9: "The cmos switch shall be treated as the combination of a
//  pmos switch and an nmos switch."
TEST(CmosSwitches, CmosIsNmosPlusPmos) {
  // With ncontrol=1, pcontrol=0: both conduct → data passes.
  // With ncontrol=0, pcontrol=1: both block → z.
  EXPECT_NE(EvalMosSwitch(SwitchType::kCmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

// §28.9: cmos has output, input, n-control, p-control (4 terminals).
// §28.9: "The rcmos switch shall be treated as the combination of an
//  rpmos switch and an rnmos switch."
// §28.9: 0-3 delays.
TEST(CmosSwitches, CmosMaxThreeDelays) {
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kCmos), 3u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRcmos), 3u);
}

}  // namespace
