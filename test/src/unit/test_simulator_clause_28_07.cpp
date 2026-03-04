#include <gtest/gtest.h>

#include "model_gate_logic.h"
#include "model_switch_eval.h"

namespace {

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

TEST(MosSwitches, ZDataAlwaysZ) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
}

}
