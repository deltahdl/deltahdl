// §28.7: MOS switches

#include <gtest/gtest.h>

#include "model_switch_eval.h"

namespace {

// =============================================================
// §28.7: MOS switches
// =============================================================
// §28.7: Truth tables (Table 28-6) — nmos conducts when control=1
TEST(MosSwitches, NmosConductsWhenControlHigh) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV1),
            Val4Ext::kV1);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kX, Val4::kV1), Val4Ext::kX);
}

TEST(MosSwitches, NmosBlocksWhenControlLow) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV0),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV0),
            Val4Ext::kZ);
}

TEST(MosSwitches, NmosXControlProducesLOrH) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kX), Val4Ext::kL);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kX), Val4Ext::kH);
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
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
}

}  // namespace
