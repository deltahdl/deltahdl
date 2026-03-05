#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §E.2: trireg net gets default_decay_time when no explicit decay.
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

// §E.2: trireg with explicit decay ignores default.
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

// §E.2: `default_decay_time infinite means no decay (decay_ticks stays 0).
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

// §E.2: no directive means infinite (default) — decay_ticks = 0.
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

// §E.2: default_decay_time does not affect non-trireg nets.
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

// §E.2: later directive overrides earlier at elaborator level.
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

// §E.2: multiple trireg nets all get the default.
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

}  // namespace
