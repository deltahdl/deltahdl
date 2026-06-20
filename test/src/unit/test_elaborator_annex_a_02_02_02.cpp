

#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
