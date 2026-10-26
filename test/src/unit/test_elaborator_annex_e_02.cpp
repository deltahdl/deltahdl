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

// C1 (real_constant) x C3: a real-valued directive still drives the decay time
// applied to a trireg. E.2 admits a real_constant and gives no conversion of
// its own, so §3.14.1 settles what it becomes -- the time precision fixes how a
// delay value is rounded before simulation uses it, and where the precision
// equals the time unit, delay values round to whole numbers. The count is
// rounded and not truncated, so 3.5 is a decay time of 4.
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

// The decay time a named net of a named module was given, or 0 with `decays`
// false when the module or the net is not in the design.
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

// Annex E.2: the directive applies to the trireg nets of the modules that
// follow it in the source, so a second directive between two modules leaves
// the first module's net under the first value and gives the second module's
// net the second value. A default read off the compilation unit's last
// directive would give both nets 200.
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
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(DecayOfNet(design, "a", "cap").ticks, 50u);
  EXPECT_EQ(DecayOfNet(design, "b", "cap").ticks, 200u);
}

// Annex E.2: a module declared before any directive has trireg nets with no
// decay time, the state E.2's infinite names, whatever directive follows it;
// and an infinite directive between two finite ones puts the module after it
// back under no decay.
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
      f, "", /*auto_top=*/true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(DecayOfNet(design, "a", "cap").decays);
  EXPECT_EQ(DecayOfNet(design, "b", "cap").ticks, 50u);
  EXPECT_TRUE(DecayOfNet(design, "b", "cap").decays);
  EXPECT_FALSE(DecayOfNet(design, "c", "cap").decays);
}

// Annex E.2 with §3.14.1: a delay value is rounded at the time precision of the
// module it is written for, and a real decay time is no exception, whichever of
// E.2's directive and a trireg's third delay (§28.16.2.2) writes it. Under
// 1ns/100ps, 2.5 is 2.5 ns, so the default reaches the net as the real 2.5 the
// lowerer rounds at the precision, as the third delay does, rather than as the
// 3 whole units of a rounding made before any precision is known.
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

// An integer argument stays the whole count it was written as, as an integer
// third delay does, so nothing is rounded twice.
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
