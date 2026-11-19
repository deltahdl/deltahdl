#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_declaration_places.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

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

TEST(TriregChargeStrength, DefaultStrengthIsMediumOnHeldOne) {
  SimFixture f;
  Net* cap = ChargeThenRelease("trireg [63:0] cap;", "{64{1'b1}}", "64'bz", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kHighz);
}

TEST(TriregChargeStrength, SmallStrengthOnHeldZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg (small) [63:0] cap;\n"
      "  assign cap = en ? 64'd0 : 64'bz;\n"
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
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kSmall);
  EXPECT_EQ(cap->resolved_strength.s0_lo, Strength::kSmall);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kHighz);
}

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

TEST(TriregChargeStrength, UnknownHeldValueDrivesBothSidesAtChargeStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en;\n"
      "  trireg (large) [63:0] cap;\n"
      "  assign cap = en ? 64'bx : 64'bz;\n"
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
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s0_lo, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kLarge);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kLarge);
}

TEST(TriregChargeStrength,
     ContinuouslyDrivenTriregDoesNotPresentChargeStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg (small) [63:0] cap;\n"
      "  assign cap = 64'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);

  auto* cap = f.ctx.FindNet("cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_FALSE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_NE(cap->resolved_strength.s1_hi, Strength::kSmall);
}

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

TEST(TriregChargeStrength, BitsHoldingOneAloneLeaveTheZeroSideHighZ) {
  SimFixture f;
  Net* cap = ChargeThenRelease("trireg [1:0] cap;", "2'b11", "2'bz", f);
  ASSERT_NE(cap, nullptr);
  EXPECT_TRUE(cap->InCapacitiveState());
  EXPECT_EQ(cap->resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(cap->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(cap->resolved_strength.s1_lo, Strength::kMedium);
}

TEST(TriregStrengthSim, LargeChargeOutranksAWeakDriver) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  trireg c;\n"
      "  trireg (large) l;\n"
      "  logic d = 1, g = 1, w = 0;\n"
      "  nmos n1 (c, d, g);\n"
      "  nmos n2 (l, d, g);\n"
      "  bufif1 (weak1, weak0) b1 (c, 1'b0, w);\n"
      "  bufif1 (weak1, weak0) b2 (l, 1'b0, w);\n"
      "  initial begin\n"
      "    #1 g = 0;\n"
      "    #1 $display(\"c=%b %v l=%b %v\", c, c, l, l);\n"
      "    w = 1;\n"
      "    #1 $display(\"c=%b %v l=%b %v\", c, c, l, l);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "c=1 Me1 l=1 La1\n"
            "c=0 We0 l=1 La1\n");
}

TEST(TriregChargeStrength, UndrivenTriregHoldsXAtItsChargeStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  trireg t;\n"
      "  trireg (large) u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* t = f.ctx.FindNet("t");
  auto* u = f.ctx.FindNet("u");
  ASSERT_NE(t, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(t->resolved->value.words[0].aval & 0x1, 1u);
  EXPECT_EQ(t->resolved->value.words[0].bval & 0x1, 1u);
  EXPECT_EQ(t->resolved_strength.s0_hi, Strength::kMedium);
  EXPECT_EQ(t->resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_EQ(u->resolved_strength.s0_hi, Strength::kLarge);
  EXPECT_EQ(u->resolved_strength.s1_hi, Strength::kLarge);
}

TEST(TriregChargeStrength, AnExplicitMediumDrivesTheHeldValueAtMedium) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  reg c = 0;\n"
      "  trireg (medium) m;\n"
      "  trireg (medium) logic [1:0] v;\n"
      "  assign m = c ? 1'bz : 1'b1;\n"
      "  assign v = c ? 2'bz : 2'b10;\n"
      "  initial begin\n"
      "    #1 c = 1;\n"
      "    #1 $display(\"%v %v %v\", m, v[1], v[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Me1 Me1 Me0\n");
}

TEST(TriregChargeStrength, AnExplicitDataTypeKeepsTheChargeStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  reg c = 0;\n"
      "  trireg (small) logic s;\n"
      "  trireg (large) logic [1:0] l;\n"
      "  trireg logic d;\n"
      "  assign s = c ? 1'bz : 1'b0;\n"
      "  assign l = c ? 2'bz : 2'b01;\n"
      "  assign d = c ? 1'bz : 1'b1;\n"
      "  initial begin\n"
      "    #1 c = 1;\n"
      "    #1 $display(\"%v %v %v %v\", s, l[1], l[0], d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Sm0 La0 La1 Me1\n");
}

TEST(TriregChargeStrength,
     ADeclaredChargeStrengthHoldsInAnInterfaceGenerateOrProgram) {
  for (auto place :
       {NetDeclarationPlace::kInterface, NetDeclarationPlace::kGenerate,
        NetDeclarationPlace::kProgram}) {
    EXPECT_EQ(NetStrengthDeclaredIn(place, "trireg (small) n;"), "SmX\n")
        << static_cast<int>(place);
    EXPECT_EQ(NetStrengthDeclaredIn(place, "trireg (large) n;"), "LaX\n")
        << static_cast<int>(place);
    EXPECT_EQ(NetStrengthDeclaredIn(place, "trireg n;"), "MeX\n")
        << static_cast<int>(place);
  }
}

TEST(TriregChargeStrength,
     DISABLED_ADeclaredChargeStrengthHoldsInTheCompilationUnit) {
  EXPECT_EQ(NetStrengthDeclaredIn(NetDeclarationPlace::kCompilationUnit,
                                  "trireg (small) n;"),
            "SmX\n");
  EXPECT_EQ(NetStrengthDeclaredIn(NetDeclarationPlace::kCompilationUnit,
                                  "trireg (large) n;"),
            "LaX\n");
}

TEST(TriregChargeStrength, TheDefaultMediumHoldsInTheCompilationUnit) {
  EXPECT_EQ(
      NetStrengthDeclaredIn(NetDeclarationPlace::kCompilationUnit, "trireg n;"),
      "MeX\n");
}

}  // namespace
