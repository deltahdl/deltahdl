#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DefaultTriregStrength_ExplicitOverridesDefault) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 100\n"
      "module t;\n"
      "  trireg (large) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.trireg_capacitance, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultTriregStrength_NoDirective) {
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
      EXPECT_EQ(net.trireg_capacitance, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultTriregStrength_DoesNotAffectWire) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 100\n"
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
      EXPECT_EQ(net.trireg_capacitance, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultTriregStrength_LaterOverrides) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 50\n"
      "`default_trireg_strength 200\n"
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
      EXPECT_EQ(net.trireg_capacitance, 200u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(Elaborator, DefaultTriregStrength_AppliesToAllTriregNets) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 75\n"
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
      EXPECT_EQ(net.trireg_capacitance, 75u);
      ++count;
    }
  }
  EXPECT_EQ(count, 2);
}

TEST(Elaborator, DefaultTriregStrength_ZeroValue) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 0\n"
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
      EXPECT_EQ(net.trireg_capacitance, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

uint32_t StrengthOfNet(const RtlirDesign* design, std::string_view module,
                       std::string_view net_name) {
  for (const auto* mod : design->top_modules) {
    if (mod->name != module) continue;
    for (const auto& net : mod->nets) {
      if (net.name == net_name) return net.trireg_capacitance;
    }
  }
  return 0;
}

TEST(Elaborator, DefaultTriregStrength_EachModuleTakesTheDirectiveBeforeIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 50\n"
      "module a;\n"
      "  trireg cap;\n"
      "endmodule\n"
      "`default_trireg_strength 200\n"
      "module b;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(StrengthOfNet(design, "a", "cap"), 50u);
  EXPECT_EQ(StrengthOfNet(design, "b", "cap"), 200u);
}

TEST(Elaborator, DefaultTriregStrength_AModuleBeforeTheDirectiveIsNotUnderIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  trireg cap;\n"
      "endmodule\n"
      "`default_trireg_strength 50\n"
      "module b;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(StrengthOfNet(design, "a", "cap"), 0u);
  EXPECT_EQ(StrengthOfNet(design, "b", "cap"), 50u);
}

TEST(Elaborator, DefaultTriregStrength_ReachesATriregOfEveryDesignElement) {
  for (const char* element :
       {"interface e;\n  trireg cap;\nendinterface\n",
        "program e;\n  trireg cap;\nendprogram\n",
        "module e;\n  if (1) begin : g\n    trireg cap;\n  end\nendmodule\n"}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        std::string("`default_trireg_strength 75\n") + element, f, "e");
    ASSERT_NE(design, nullptr) << element;
    EXPECT_FALSE(f.has_errors) << element;
    uint32_t strength = 0;
    for (const auto* mod : design->top_modules) {
      for (const auto& net : mod->nets) {
        if (net.name.ends_with("cap")) strength = net.trireg_capacitance;
      }
    }
    EXPECT_EQ(strength, 75u) << element;
  }
}

TEST(Elaborator,
     DISABLED_DefaultTriregStrength_InsideAModuleReachesOnlyLaterNets) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 50\n"
      "module t;\n"
      "  trireg early;\n"
      "`default_trireg_strength 200\n"
      "  trireg late;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(StrengthOfNet(design, "t", "early"), 50u);
  EXPECT_EQ(StrengthOfNet(design, "t", "late"), 200u);
}

}  // namespace
