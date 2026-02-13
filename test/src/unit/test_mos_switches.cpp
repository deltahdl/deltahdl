#include <gtest/gtest.h>

#include <cstdint>

// --- Local types for MOS/pass switches (§28.7, §28.8, §28.9) ---

enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };
enum class Val4Ext : uint8_t {
  kV0 = 0, kV1 = 1, kX = 2, kZ = 3, kL = 4, kH = 5
};

enum class SwitchType : uint8_t {
  kNmos, kPmos, kRnmos, kRpmos,
  kTran, kRtran,
  kTranif0, kTranif1, kRtranif0, kRtranif1,
  kCmos, kRcmos,
};

Val4Ext EvalMosSwitch(SwitchType type, Val4 data, Val4 control);
bool IsBidirectional(SwitchType type);
bool AcceptsDelaySpec(SwitchType type);
uint32_t MaxSwitchDelays(SwitchType type);

// =============================================================
// §28.7: MOS switches
// =============================================================

// §28.7: Truth tables (Table 28-6) — nmos conducts when control=1
TEST(MosSwitches, NmosConductsWhenControlHigh) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV1),
            Val4Ext::kV1);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kX, Val4::kV1),
            Val4Ext::kX);
}

TEST(MosSwitches, NmosBlocksWhenControlLow) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV0),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV0),
            Val4Ext::kZ);
}

TEST(MosSwitches, NmosXControlProducesLOrH) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kX),
            Val4Ext::kL);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kX),
            Val4Ext::kH);
}

// §28.7: pmos conducts when control=0 (complementary)
TEST(MosSwitches, PmosConductsWhenControlLow) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV0, Val4::kV0),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV1, Val4::kV0),
            Val4Ext::kV1);
}

TEST(MosSwitches, PmosBlocksWhenControlHigh) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV0, Val4::kV1),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

// §28.7: z data always produces z regardless of control.
TEST(MosSwitches, ZDataAlwaysZ) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV0),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV0),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
}

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
