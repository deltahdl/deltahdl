// §28.9: CMOS switches

#include <gtest/gtest.h>

#include "model_switch_eval.h"

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
