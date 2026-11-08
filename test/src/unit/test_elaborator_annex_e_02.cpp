#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DefaultDecayTime_AppliesToTrireg) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 100\n"
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
      EXPECT_EQ(net.decay_ticks, 100u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultDecayTime_ExplicitOverridesDefault) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 100\n"
      "module t;\n"
      "  trireg #(1, 1, 50) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 50u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultDecayTime_InfiniteNoDecay) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time infinite\n"
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

TEST(Elaborator, DefaultDecayTime_NoDirectiveMeansInfinite) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
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

TEST(Elaborator, DefaultDecayTime_DoesNotAffectWire) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 100\n"
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "w") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultDecayTime_LaterOverridesAtElabLevel) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 50\n"
      "`default_decay_time 200\n"
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
      EXPECT_EQ(net.decay_ticks, 200u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultDecayTime_RealArgumentAppliesToTrireg) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 3.5\n"
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
      EXPECT_EQ(net.decay_ticks, 4u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultDecayTime_AppliesToAllTriregNets) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 75\n"
      "module t;\n"
      "  trireg a;\n"
      "  trireg b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& net : mod->nets) {
    if (net.name == "a" || net.name == "b") {
      EXPECT_EQ(net.decay_ticks, 75u);
      ++count;
    }
  }
  EXPECT_EQ(count, 2);
}

struct DecayOf {
  uint64_t ticks = 0;
  bool decays = false;
  bool is_real = false;
  double real = 0.0;
};
DecayOf DecayOfNet(const RtlirDesign* design, std::string_view module,
                   std::string_view net_name) {
  for (const auto* mod : design->top_modules) {
    if (mod->name != module) continue;
    for (const auto& net : mod->nets) {
      if (net.name == net_name) {
        return {net.decay_ticks, net.decays, net.decay_is_real, net.decay_real};
      }
    }
  }
  return {};
}

TEST(Elaborator, DefaultDecayTime_EachModuleTakesTheDirectiveBeforeIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 50\n"
      "module a;\n"
      "  trireg cap;\n"
      "endmodule\n"
      "`default_decay_time 200\n"
      "module b;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(DecayOfNet(design, "a", "cap").ticks, 50u);
  EXPECT_EQ(DecayOfNet(design, "b", "cap").ticks, 200u);
}

TEST(Elaborator, DefaultDecayTime_AModuleBeforeTheDirectiveIsNotUnderIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  trireg cap;\n"
      "endmodule\n"
      "`default_decay_time 50\n"
      "module b;\n"
      "  trireg cap;\n"
      "endmodule\n"
      "`default_decay_time infinite\n"
      "module c;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(DecayOfNet(design, "a", "cap").decays);
  EXPECT_EQ(DecayOfNet(design, "b", "cap").ticks, 50u);
  EXPECT_TRUE(DecayOfNet(design, "b", "cap").decays);
  EXPECT_FALSE(DecayOfNet(design, "c", "cap").decays);
}

TEST(Elaborator, DefaultDecayTime_RealArgumentReachesTheNetUnrounded) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns/100ps\n"
      "`default_decay_time 2.5\n"
      "module t;\n"
      "  trireg by_default;\n"
      "  trireg #(0, 0, 2.5) declared;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const DecayOf kByDefault = DecayOfNet(design, "t", "by_default");
  const DecayOf kDeclared = DecayOfNet(design, "t", "declared");
  EXPECT_TRUE(kByDefault.decays);
  EXPECT_TRUE(kByDefault.is_real);
  EXPECT_EQ(kByDefault.real, 2.5);
  EXPECT_EQ(kByDefault.is_real, kDeclared.is_real);
  EXPECT_EQ(kByDefault.real, kDeclared.real);
}

TEST(Elaborator, DefaultDecayTime_IntegerArgumentReachesTheNetAsACount) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_decay_time 1_000\n"
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const DecayOf kDecay = DecayOfNet(design, "t", "cap");
  EXPECT_EQ(kDecay.ticks, 1000u);
  EXPECT_FALSE(kDecay.is_real);
}

}  // namespace
