// Tests for §6.3.2.1 "Charge strength", which confines the charge strength
// specification to trireg nets, names small, medium and large as its keywords,
// and makes medium the default charge strength of a trireg net.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ChargeStrengthElaboration, TriregDefaultChargeStrengthMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "a") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.3.2.1 states "The charge strength specification shall be used only with
// trireg nets", so `small` on a wire is rejected under §6.3.2.1 and not under
// §10.3, whose footnote 16 to Syntax 10-1 only annotates the net_declaration
// production with the same restriction. Parser::ParseNetStrength raises the
// report where it reads the specification, and ElaborateSrc leaves it in the
// fixture's engine.
TEST(ChargeStrengthElaboration, SmallOnNonTriregIsIllegal) {
  ElabFixture f;
  // The charge-strength rule is reported while parsing, so this case reaches
  // its subject through a source that does not parse.
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  wire (small) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

// An explicit `medium` charge strength on a trireg is carried to the net as
// Strength::kMedium through the parser->elaborator override path (charge code
// 2), which is a different production path than the default-retention path that
// the no-strength trireg tests exercise. This completes the small/medium/large
// value-mapping trio at the elaboration stage.
TEST(ChargeStrengthElaboration, TriregExplicitMediumPreservesMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (medium) cm;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cm") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, TriregVectorDefaultsToMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg [3:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "bus") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, TriregWithDelayDefaultsToMedium) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg #(0,0,50) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.charge_strength, Strength::kMedium);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, TriregLargeWithDelayPreservesLarge) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (large) #(0,0,50) cap1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap1") {
      EXPECT_EQ(net.charge_strength, Strength::kLarge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeStrengthElaboration, TriregSmallSignedVectorPreservesSmall) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap2") {
      EXPECT_EQ(net.charge_strength, Strength::kSmall);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
