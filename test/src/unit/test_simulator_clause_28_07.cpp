#include <gtest/gtest.h>

#include "model_gate_logic.h"
#include "model_switch_eval.h"

namespace {

TEST(MosSwitchSimulation, NmosConductsWhenControlHigh) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV1),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV1),
            Val4Ext::kV1);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kX, Val4::kV1), Val4Ext::kX);
}

TEST(MosSwitchSimulation, NmosBlocksWhenControlLow) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kV0),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kV0),
            Val4Ext::kZ);
}

TEST(MosSwitchSimulation, NmosXControlProducesLOrH) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV0, Val4::kX), Val4Ext::kL);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kV1, Val4::kX), Val4Ext::kH);
}

TEST(MosSwitchSimulation, PmosConductsWhenControlLow) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV0, Val4::kV0),
            Val4Ext::kV0);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV1, Val4::kV0),
            Val4Ext::kV1);
}

TEST(MosSwitchSimulation, PmosBlocksWhenControlHigh) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV0, Val4::kV1),
            Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kV1, Val4::kV1),
            Val4Ext::kZ);
}

// §28.7 states the four MOS switches are unidirectional channels for data
// (paralleling the bufif gates). The claim applies equally to the
// resistive variants, so all four kinds must classify as non-bidirectional.
TEST(MosSwitchSimulation, MosSwitchesNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kNmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kPmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRnmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kRpmos));
}

TEST(MosSwitchSimulation, ZDataAlwaysZ) {
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV0), Val4Ext::kZ);
  EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, Val4::kZ, Val4::kV1), Val4Ext::kZ);
}

// Exhaustive 16-cell coverage of the nmos logic table. The per-scenario
// tests above document specific §28.7 claims by name; this test pins
// every (data, control) pair so missing cells (notably the Z-control and
// X-data rows) cannot regress silently.
TEST(MosSwitchSimulation, NmosFullTruthTable) {
  struct {
    Val4 data;
    Val4 ctrl;
    Val4Ext expected;
  } const cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ},
      {Val4::kX, Val4::kV0, Val4Ext::kZ},
      {Val4::kZ, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kV0},
      {Val4::kV1, Val4::kV1, Val4Ext::kV1},
      {Val4::kX, Val4::kV1, Val4Ext::kX},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kZ},
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kZ},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalMosSwitch(SwitchType::kNmos, c.data, c.ctrl), c.expected);
  }
}

// Exhaustive 16-cell coverage of the pmos logic table — same rationale
// as NmosFullTruthTable. pmos conducts on control==0 so the 0/1 columns
// are swapped relative to nmos; the X/Z columns mirror nmos because
// uncertain control collapses to the same L/H/X/Z outputs.
TEST(MosSwitchSimulation, PmosFullTruthTable) {
  struct {
    Val4 data;
    Val4 ctrl;
    Val4Ext expected;
  } const cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kV1},
      {Val4::kX, Val4::kV0, Val4Ext::kX},
      {Val4::kZ, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kZ},
      {Val4::kX, Val4::kV1, Val4Ext::kZ},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kZ},
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kZ},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalMosSwitch(SwitchType::kPmos, c.data, c.ctrl), c.expected);
  }
}

// Table 28-6 groups rnmos with nmos and rpmos with pmos: the resistive
// variants share the same logic table. These tests pin every cell so the
// simulator cannot silently diverge between resistive and non-resistive
// MOS. Strength attenuation is a separate concern modeled elsewhere.
TEST(MosSwitchSimulation, RnmosMatchesNmosTruthTable) {
  struct {
    Val4 data;
    Val4 ctrl;
    Val4Ext expected;
  } const cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kZ},
      {Val4::kV1, Val4::kV0, Val4Ext::kZ},
      {Val4::kX, Val4::kV0, Val4Ext::kZ},
      {Val4::kZ, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kV0},
      {Val4::kV1, Val4::kV1, Val4Ext::kV1},
      {Val4::kX, Val4::kV1, Val4Ext::kX},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kZ},
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kZ},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalMosSwitch(SwitchType::kRnmos, c.data, c.ctrl), c.expected);
  }
}

TEST(MosSwitchSimulation, RpmosMatchesPmosTruthTable) {
  struct {
    Val4 data;
    Val4 ctrl;
    Val4Ext expected;
  } const cases[] = {
      {Val4::kV0, Val4::kV0, Val4Ext::kV0},
      {Val4::kV1, Val4::kV0, Val4Ext::kV1},
      {Val4::kX, Val4::kV0, Val4Ext::kX},
      {Val4::kZ, Val4::kV0, Val4Ext::kZ},
      {Val4::kV0, Val4::kV1, Val4Ext::kZ},
      {Val4::kV1, Val4::kV1, Val4Ext::kZ},
      {Val4::kX, Val4::kV1, Val4Ext::kZ},
      {Val4::kZ, Val4::kV1, Val4Ext::kZ},
      {Val4::kV0, Val4::kX, Val4Ext::kL},
      {Val4::kV1, Val4::kX, Val4Ext::kH},
      {Val4::kX, Val4::kX, Val4Ext::kX},
      {Val4::kZ, Val4::kX, Val4Ext::kZ},
      {Val4::kV0, Val4::kZ, Val4Ext::kL},
      {Val4::kV1, Val4::kZ, Val4Ext::kH},
      {Val4::kX, Val4::kZ, Val4Ext::kX},
      {Val4::kZ, Val4::kZ, Val4Ext::kZ},
  };
  for (const auto& c : cases) {
    EXPECT_EQ(EvalMosSwitch(SwitchType::kRpmos, c.data, c.ctrl), c.expected);
  }
}

}  // namespace
