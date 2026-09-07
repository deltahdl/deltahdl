#include <gtest/gtest.h>

#include <string>

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
// (net.cpp ResolveTriregCharge) is read back from the SimContext.
//
// The charge lands on the side of the scale the held value names -- the 0 side
// for a held 0, the 1 side for a held 1, both for a held x -- and the value the
// net retains in the capacitive state is a value per bit (§6.6.4), so a vector
// whose bits do not agree is charged on both sides. The net reports one
// strength for the whole of itself, which is the range spanning what its bits
// hold, so "the opposite side stays high impedance" is a claim about a value
// every bit of which is alike and not about the width of the declaration.
//
// A [63:0] vector is used in most cases so that the released "z" driver is a
// full machine word of high impedance, which is exactly the charge storage
// state the rule speaks of; the narrow cases below are the ones about bits that
// disagree. (Whether a trireg enters that state -- the
// retain-last-value-when-drivers- turn-off rule -- belongs to §28.16.2; here we
// only observe the *strength* of the resulting charge-storage drive, which is
// §28.15.2's rule.)

// Charges a trireg declared as `decl` to `charged`, then releases its only
// driver to `released`, and returns the net in the charge storage state, so
// cases differ only in the declaration and the value they name.
Net* ChargeThenRelease(const std::string& decl, const std::string& charged,
                       const std::string& released, SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  " +
          decl +
          "\n"
          "  assign cap = en ? " +
          charged + " : " + released +
          ";\n"
          "  initial begin\n"
          "    en = 1'b1;\n"
          "    #1;\n"
          "    en = 1'b0;\n"
          "    #1;\n"
          "  end\n"
          "endmodule\n",
      f);
  if (design == nullptr || f.has_errors) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("cap");
}

// A trireg declared with no charge strength retains its charge at the medium
// default. Charged to 1 on every bit then released, its drive is medium on the
// 1 side and nothing at all on the 0 side. The value is spelled as sixty-four
// ones rather than as 64'd1, which charges bit 0 high and the other sixty-three
// low and so says nothing about which side a held 1 lands on.
TEST(TriregChargeStrength, DefaultStrengthIsMediumOnHeldOne) {
  SimFixture f;
  Net* cap = ChargeThenRelease("trireg [63:0] cap;", "{64{1'b1}}", "64'bz", f);
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
// on every bit then released, its drive is large on the 1 side, and the
// declared strength is what moved rather than the side.
TEST(TriregChargeStrength, LargeStrengthOnHeldOne) {
  SimFixture f;
  Net* cap =
      ChargeThenRelease("trireg (large) [63:0] cap;", "{64{1'b1}}", "64'bz", f);
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

// §6.6.4 has a trireg retain "its last driven value", and that value is one per
// bit; §28.12 resolves each bit of a net on its own. So a vector whose bits do
// not hold the same value is charged on both sides of the scale at once, and
// the pair the net reports spans them. Bit 0 holds 1 and bit 1 holds 0 here,
// and reading either bit alone would report one side and call the other high
// impedance.
TEST(TriregChargeStrength, BitsHoldingDifferentValuesChargeBothSides) {
  SimFixture f;
  Net* cap = ChargeThenRelease("trireg [1:0] cap;", "2'b01", "2'bz", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s0_lo, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kMedium);
}

// The same net charged so that its bits do agree: every bit holds 1, so the
// charge is on the 1 side alone and the 0 side stays at high impedance. Without
// this, a fold that put the charge on both sides whatever the bits held would
// pass the case above.
TEST(TriregChargeStrength, BitsHoldingOneAloneLeaveTheZeroSideHighZ) {
  SimFixture f;
  Net* cap = ChargeThenRelease("trireg [1:0] cap;", "2'b11", "2'bz", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kMedium);
}

}  // namespace
