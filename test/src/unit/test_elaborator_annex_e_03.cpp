#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §E.3: trireg net gets default_trireg_strength when no explicit charge.
TEST(Elaborator, DefaultTriregStrength_AppliesToTrireg) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_trireg_strength 100\n"
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
      EXPECT_EQ(net.trireg_capacitance, 100u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §E.3: trireg with explicit charge strength ignores default.
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

// §E.3: no directive means no capacitance override.
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

// §E.3: default_trireg_strength does not affect non-trireg nets.
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

// §E.3: later directive overrides earlier at elaborator level.
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

// §E.3: multiple trireg nets all get the default.
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

// §E.3: value zero is valid.
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

}  // namespace
