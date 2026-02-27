// §28.8: Bidirectional pass switches

#include <gtest/gtest.h>

#include "model_switch_eval.h"

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

}  // namespace
