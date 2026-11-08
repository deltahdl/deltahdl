#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StaticDeferredAssertion, ModuleLevelDeferredAssertBecomesAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  a1: assert #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
  ASSERT_NE(mod->processes[0].body, nullptr);
  EXPECT_TRUE(mod->processes[0].body->is_deferred);
}

TEST(StaticDeferredAssertion, EquivalentToExplicitAlwaysCombWrapping) {
  ElabFixture statik;
  auto* static_design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  a1: assert #0 (a == b);\n"
      "endmodule\n",
      statik);
  ASSERT_NE(static_design, nullptr);
  EXPECT_FALSE(statik.has_errors);

  ElabFixture explicit_form;
  auto* explicit_design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  always_comb begin\n"
      "    a1: assert #0 (a == b);\n"
      "  end\n"
      "endmodule\n",
      explicit_form);
  ASSERT_NE(explicit_design, nullptr);
  EXPECT_FALSE(explicit_form.has_errors);

  ASSERT_EQ(static_design->top_modules.size(), 1u);
  ASSERT_EQ(explicit_design->top_modules.size(), 1u);
  const auto& sp = static_design->top_modules[0]->processes;
  const auto& ep = explicit_design->top_modules[0]->processes;
  ASSERT_EQ(sp.size(), 1u);
  ASSERT_EQ(ep.size(), 1u);
  EXPECT_EQ(sp[0].kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_EQ(ep[0].kind, RtlirProcessKind::kAlwaysComb);
}

TEST(StaticDeferredAssertion, NamelessDeferredAssertElaboratesCleanly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  assert #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
}

TEST(StaticDeferredAssertion, ModuleLevelFinalDeferredAssertBecomesAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  a2: assert final (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
  ASSERT_NE(mod->processes[0].body, nullptr);
  EXPECT_TRUE(mod->processes[0].body->is_final_deferred);
}

TEST(StaticDeferredAssertion,
     MultipleStaticDeferredAssertionsEachBecomeAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b, c);\n"
      "  a1: assert #0 (a == b);\n"
      "  a2: assert #0 (b == c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_EQ(mod->processes[1].kind, RtlirProcessKind::kAlwaysComb);
}

TEST(StaticDeferredAssertion, ConcurrentAssertNotWrappedInAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic clk, a);\n"
      "  ap: assert property (@(posedge clk) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysFF);
}

}  // namespace
