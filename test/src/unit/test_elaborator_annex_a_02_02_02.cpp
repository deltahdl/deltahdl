// §A.2.2.2: elaborator-stage coverage of the drive_strength production. The
// BNF lists six valid alternatives — every same-direction pair, and the two
// both-highz pairs, are outside the production and must be rejected; the four
// strength0/strength1 keywords must each round-trip cleanly.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §A.2.2.2 drive_strength has no `( highz0 , highz1 )` or `( highz1 , highz0 )`
// alternative; both forms — and every host construct that accepts a
// drive_strength — must reject the pair.
TEST(StrengthPairElaboration, GateInstanceHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz0, highz1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstanceHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz1, highz0) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, NetDeclHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, NetDeclHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, ContAssignHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, ContAssignHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.2.2.2 alternatives 3-6 each pair one highz keyword with one strength
// keyword; those mixed pairs must elaborate without complaint.
TEST(StrengthPairElaboration, GateInstanceHighz0WithStrong1IsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz0, strong1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.2.2.2 alternatives 1-2 cover (strength0, strength1) and its reverse; the
// elaborator must accept any of the four strength0/strength1 keyword pairs.
TEST(StrengthPairElaboration, GateInstanceStrongPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (strong0, strong1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstanceSupplyPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (supply0, supply1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstancePullPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (pull0, pull1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstanceWeakPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (weak0, weak1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.2.2.2 drive_strength applies wherever a strength spec is permitted; a
// continuous assignment with a valid strength pair must elaborate cleanly.
TEST(StrengthPairElaboration, ContAssignStrongPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.2.2.2 alternative 1 — `( strength0 , strength1 )` — must round-trip from
// source through elaboration with each keyword distinguishable in the recorded
// drive_strength fields. The fields encode 1=highz, 2=weak, 3=pull, 4=strong,
// 5=supply, so a successful elaboration both confirms BNF acceptance and pins
// down that the parser preserved each keyword separately.

TEST(StrengthPairElaboration, Form1SupplyPairEncodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(StrengthPairElaboration, Form1StrongWeakPairEncodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 4u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 2u);
}

TEST(StrengthPairElaboration, Form1PullSupplyPairEncodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 3u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(StrengthPairElaboration, Form1OnNetDeclEncodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire (supply0, supply1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

// §A.2.2.2 alternative 2 — `( strength1 , strength0 )` — the reversed-order
// form must elaborate with strength0/strength1 fields assigned by position
// (slot 0 = value-0 strength, slot 1 = value-1 strength) regardless of source
// order.

TEST(StrengthPairElaboration, Form2PullSupplyEncodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 3u);
}

TEST(StrengthPairElaboration, Form2StrongWeakOnNetDeclEncodes) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire (strong1, weak0) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

// §A.2.2.2 alternatives 3 and 4 — `( strength0 , highz1 )` and
// `( strength1 , highz0 )` — pair a strength keyword in its native slot with
// highz in the opposite slot. The elaborator must encode highz as 1 and keep
// the strength keyword distinguishable.

TEST(StrengthPairElaboration, Form3Strong0Highz1Encodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 4u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 1u);
}

TEST(StrengthPairElaboration, Form4Strong1Highz0Encodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong1, highz0) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

// §A.2.2.2 alternatives 5 and 6 — `( highz0 , strength1 )` and
// `( highz1 , strength0 )` — must elaborate with highz encoded as 1 in its
// own slot and the strength keyword preserved in the other slot.

TEST(StrengthPairElaboration, Form5Highz0Strong1Encodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

TEST(StrengthPairElaboration, Form5Highz0Supply1Encodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, supply1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
}

TEST(StrengthPairElaboration, Form6Highz1Weak0Encodes) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, weak0) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 1u);
}

// §A.2.2.2 charge_strength — `( small ) | ( medium ) | ( large )` — must
// elaborate to the matching Strength enum value so downstream consumers can
// distinguish the three storage tiers.

TEST(ChargeStrengthElaboration, SmallEncodesAsSmall) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (small) s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "s") {
      EXPECT_EQ(net.charge_strength, Strength::kSmall);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, MediumEncodesAsMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "m") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, LargeEncodesAsLarge) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (large) l;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "l") {
      EXPECT_EQ(net.charge_strength, Strength::kLarge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
