#include <gtest/gtest.h>

#include "model_gate_logic.h"
#include "model_switch_eval.h"

namespace {

TEST(CmosSwitches, CmosIsNmosPlusPmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kCmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, RcmosIsRnmosPlusRpmos) {
  EXPECT_NE(EvalMosSwitch(SwitchType::kRcmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

TEST(CmosSwitches, CmosMaxThreeDelays) {
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kCmos), 3u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRcmos), 3u);
}

// cmos/rcmos accept delays per the delay3 grammar in §28.9.
TEST(CmosSwitches, CmosAcceptsDelaySpec) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kCmos));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRcmos));
}

// cmos/rcmos are unidirectional: output is driven from data, never the reverse.
TEST(CmosSwitches, CmosIsNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kCmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRcmos));
}

// With data=Z the cmos pair cannot drive the output, regardless of controls.
TEST(CmosSwitches, CmosBlocksHighZData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kZ, Val4::kV1),
            Val4Ext::kZ);
}

// A conducting cmos drives a clean logic 0 when data=0 — the n-half carries
// the low level through without inversion.
TEST(CmosSwitches, CmosPassesZeroData) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kCmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kRcmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
}

}  // namespace
