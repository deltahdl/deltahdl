#include "fixture_elaborator.h"

using namespace delta;

// §16.4.3 Deferred assertions outside procedural code.
//
// A deferred assertion statement that appears outside procedural code is a
// "static deferred assertion" and shall be treated as if it were contained in
// an always_comb procedure. The elaborator carries this rule by building an
// implicit always_comb process whose body is the deferred assertion statement,
// so the assertion runs once at time zero and re-evaluates whenever one of its
// operands changes — exactly the behaviour of always_comb.

namespace {

// The deferred assertion outside procedural code becomes an always_comb
// process rather than being dropped or treated as a concurrent assertion.
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

// The static deferred assertion is exactly equivalent to wrapping the same
// statement in an always_comb begin ... end block: both yield one always_comb
// process with a deferred body.
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

// A nameless static deferred assertion is legal: the always_comb treatment
// means it is not subject to the "must be named" rule of a concurrent
// assertion / clocking item.
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

// A final deferred assertion outside procedural code is likewise treated as a
// static deferred assertion, producing an always_comb process.
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

// A deferred cover outside procedural code is also a static deferred
// assertion and is wrapped in always_comb.
TEST(StaticDeferredAssertion, ModuleLevelDeferredCoverBecomesAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  c1: cover #0 (a != b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
}

// A deferred assume outside procedural code is also a static deferred
// assertion: the always_comb treatment applies to every deferred immediate
// directive (assert, assume, cover), not only to assert.
TEST(StaticDeferredAssertion, ModuleLevelDeferredAssumeBecomesAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m (input logic a, b);\n"
      "  m1: assume #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kAlwaysComb);
  ASSERT_NE(mod->processes[0].body, nullptr);
  EXPECT_TRUE(mod->processes[0].body->is_deferred);
}

// Several static deferred assertions in one module each get their own implicit
// always_comb process, just as several separate always_comb procedures would.
TEST(StaticDeferredAssertion, MultipleStaticDeferredAssertionsEachBecomeAlwaysComb) {
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

// A concurrent property assertion at module level is NOT a deferred assertion,
// so it is not turned into an always_comb process — confirming the rule keys
// strictly on the deferred form.
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
  EXPECT_EQ(mod->processes.size(), 0u);
}

}  // namespace
