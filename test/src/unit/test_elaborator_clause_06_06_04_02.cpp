#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.6.4.2: Trireg with explicit three-delay spec extracts decay_ticks.
TEST(Elaborator, Sec6_6_4_2_ExplicitDecayTime) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg (large) #(0, 0, 50) cap1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap1") {
      EXPECT_EQ(net.decay_ticks, 50u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.6.4.2: Trireg without decay spec has decay_ticks = 0 (ideal capacitive).
TEST(Elaborator, Sec6_6_4_2_NoDecaySpecMeansIdeal) {
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

// §6.6.4.2: Trireg with two delays (rise, fall) but no decay — ideal.
TEST(Elaborator, Sec6_6_4_2_TwoDelayNoDecayIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(3, 5) cap;\n"
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

// §6.6.4.2: Decay time of zero means no decay (ideal capacitive).
TEST(Elaborator, Sec6_6_4_2_DecayTimeZeroIsIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1, 1, 0) cap;\n"
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

}  // namespace
