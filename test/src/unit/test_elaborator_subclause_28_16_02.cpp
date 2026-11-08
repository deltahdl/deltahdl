#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ChargeDecayElaboration, NoDecaySpecMeansIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecayElaboration, ThirdDelayBecomesDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(2, 4, 17) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 17u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecayElaboration, DecayTimeFromParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int P = 21);\n"
      "  trireg #(2, 4, P) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 21u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecayElaboration, DecayTimeFromLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int LP = 13;\n"
      "  trireg #(2, 4, LP) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 13u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecayElaboration, DecayTimeIsTheThirdTripleWhenEveryDelayIsATriple) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1:2:3, 4:5:6, 7:8:9) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 8u);
}

TEST(ChargeDecayElaboration, ThirdDelayOfANonTriregIsNoChargeDecayTime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire #(1, 2, 3) w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindNet(design, "t", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->decay_ticks, 0u);
  EXPECT_FALSE(w->decays);
  ASSERT_NE(w->delay_turnoff, nullptr);
  EXPECT_EQ(w->delay_turnoff->int_val, 3u);
}

TEST(ChargeDecayElaboration, ThirdDelayOfATriregIsTheChargeDecayTime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1, 2, 3) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 3u);
  EXPECT_TRUE(cap->decays);
}

TEST(ChargeDecayElaboration, DefaultDecayTimeDoesNotReachANonTrireg) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 100\n"
      "module t;\n"
      "  wire #(1, 2, 3) w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindNet(design, "t", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->decay_ticks, 0u);
  EXPECT_FALSE(w->decays);
}

TEST(ChargeDecayElaboration, RealThirdDelayRoundsToADecayTime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(0, 0, 50.5) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 51u);
  EXPECT_TRUE(cap->decays);
}

TEST(ChargeDecayElaboration, RealDirectiveAndRealThirdDelayAgree) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 50.5\n"
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 51u);
  EXPECT_TRUE(cap->decays);
}

}  // namespace
