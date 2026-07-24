#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §28.15.2 states a runtime rule: a trireg net models a charge storage node,
// and once a driver has charged it and then gone to high impedance the net
// enters the charge storage state and holds its last value. The drive resulting
// from that retained charge carries the trireg's charge strength -- one of
// large, medium, or small -- specified by the user in the net declaration, and
// medium by default. The charge strength is produced by the `trireg (strength)`
// declaration (syntax per the §6.7 dependency), so every test here builds the
// net from real source and drives it through parse -> elaborate -> lower ->
// run: an initial block charges the trireg to a value, then releases every
// driver to z, and the resolved strength installed by production
// (net.cpp ResolveTriregCharge) is read back from the SimContext. The held
// value lands its charge strength on the matching side (0 side for a held 0,
// 1 side for a held 1); the opposite side stays high impedance.
//
// A [63:0] vector is used so that the released "z" driver is a full machine
// word of high impedance, which is exactly the charge storage state the rule
// speaks of. (Whether a trireg enters that state -- the
// retain-last-value-when-drivers- turn-off rule -- belongs to §28.16.2; here we
// only observe the *strength* of the resulting charge-storage drive, which is
// §28.15.2's rule.)

// A trireg declared with no charge strength retains its charge at the medium
// default. Charged to 1 then released, its drive is medium on the 1 side.
TEST(TriregChargeStrength, DefaultStrengthIsMediumOnHeldOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg [63:0] cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to 1
      "    #1;\n"
      "    en = 1'b0;\n"  // release: sole driver goes to z -> charge storage
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // held 1
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kHighz);  // opposite side Z
}

// A trireg declared (small) retains its charge at small strength. Charged to 0
// then released, its drive is small on the 0 side and high impedance on the 1
// side, since the storage drive carries only the value it retained.
TEST(TriregChargeStrength, SmallStrengthOnHeldZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg (small) [63:0] cap;\n"
      "  assign cap = en ? 64'd0 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to 0
      "    #1;\n"
      "    en = 1'b0;\n"  // release -> charge storage
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 0u);  // held 0
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kSmall);
  EXPECT_EQ(cap->resolved_strength.s0_lo, Strength::kSmall);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kHighz);  // opposite side Z
}

// A trireg declared (large) retains its charge at large strength. Charged to 1
// then released, its drive is large on the 1 side.
TEST(TriregChargeStrength, LargeStrengthOnHeldOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg (large) [63:0] cap;\n"
      "  assign cap = en ? 64'd1 : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1;\n"
      "    en = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kHighz);
}

// Edge input form: a trireg that stored an unknown value is still in the charge
// storage state, so its drive carries the charge strength; the held value being
// ambiguous, that strength appears on both the 0 and 1 sides.
TEST(TriregChargeStrength, UnknownHeldValueDrivesBothSidesAtChargeStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg (large) [63:0] cap;\n"
      "  assign cap = en ? 64'bx : 64'bz;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"  // charge cap to x
      "    #1;\n"
      "    en = 1'b0;\n"  // release -> charge storage holding x
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // held x
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s0_lo, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kLarge);
}

// Negative form: the charge strength governs only the charge storage state. A
// trireg that keeps an active driver is not storing charge, so its drive is the
// driver's strength (strong for a plain continuous assign), never the declared
// small charge strength. This marks the boundary of §28.15.2's rule.
TEST(TriregChargeStrength,
     ContinuouslyDrivenTriregDoesNotPresentChargeStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg (small) [63:0] cap;\n"
      "  assign cap = 64'd1;\n"  // always driven: never enters charge storage
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);  // follows driver
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_NE(cap->resolved_strength.s1_hi, Strength::kSmall);
}

}  // namespace
