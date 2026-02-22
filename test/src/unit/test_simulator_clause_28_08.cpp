// §28.8: Bidirectional pass switches

#include <cstdint>
#include <gtest/gtest.h>

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
  if (data == Val4::kZ)
    return Val4Ext::kZ;

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
      break; // x/z stay as-is
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
  return Val4Ext::kX; // Unreachable.
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
  return 0; // Unreachable.
}

namespace {

// =============================================================
// §28.8: Bidirectional pass switches
// =============================================================
// §28.8: tran and rtran are bidirectional.
TEST(BidrectionalSwitches, TranIsBidirectional) {
  EXPECT_TRUE(IsBidirectional(SwitchType::kTran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kRtran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif0));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif1));
}

TEST(BidrectionalSwitches, MosSwitchesNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kNmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kPmos));
}

// §28.8: "The tran and rtran devices cannot be turned off; they shall
//  always pass signals."
// §28.8: "tran and rtran devices shall not accept delay specifications."
TEST(BidrectionalSwitches, TranNoDelays) {
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kTran));
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kRtran));
}

// §28.8: tranif/rtranif accept 0-2 delays.
TEST(BidrectionalSwitches, TranifAcceptsDelays) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif0));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif1));
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif0), 2u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif1), 2u);
}

} // namespace
