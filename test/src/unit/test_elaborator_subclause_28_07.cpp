

#include "fixture_elaborator.h"
#include "helpers_gate_elab.h"

using namespace delta;

namespace {

TEST(MosSwitchElaboration, OutputIsFirstTerminal) {
  ElabFixture f;
  const auto* assign = ElaborateSingleGateAssign("nmos n1(y, a, en);", f);
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(assign->lhs, nullptr);
  EXPECT_EQ(assign->lhs->text, "y");
}

TEST(MosSwitchElaboration, NmosLowersToTernaryWithZOnBlocked) {
  ElabFixture f;
  ExpectConductsAOnEnableElseZ("nmos n1(y, a, en);", f);
}

TEST(MosSwitchElaboration, PmosLowersToTernaryWithZOnActiveControl) {
  ElabFixture f;
  ExpectZOnTrueArmConductsAOnFalseArm("pmos p1(y, a, en);", f);
}

TEST(MosSwitchElaboration, RnmosConductsOnOneWithoutInverting) {
  ElabFixture f;
  ExpectConductsAOnTrueArmZOnFalseArm("rnmos r1(y, a, en);", f);
}

TEST(MosSwitchElaboration, RpmosConductsOnZeroWithoutInverting) {
  ElabFixture f;
  ExpectZOnTrueArmConductsAOnFalseArm("rpmos r1(y, a, en);", f);
}

}  // namespace
