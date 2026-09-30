#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/checker_instance_scheduling.h"

using namespace delta;

namespace {

TEST(CheckerInstanceScheduling, ProceduralVersusStaticClassification) {
  // §17.3: a checker instantiation in procedural code is a procedural checker
  // instance; one outside procedural code is a static checker instance.
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/true),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(ClassifyCheckerInstance(/*instantiated_in_procedural_code=*/false),
            CheckerInstanceKind::kStatic);
}

TEST(CheckerInstanceScheduling, OnlyStaticAssertionsAreExemptFromEveryStep) {
  // §17.3: all contents other than static assertion statements exist during
  // every time step; static assertion statements are the exception.
  EXPECT_TRUE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/false));
  EXPECT_FALSE(CheckerContentExistsEveryTimeStep(
      /*is_static_assertion_statement=*/true));
}

TEST(CheckerInstanceScheduling, StaticConcurrentAssertionTreatment) {
  // §17.3: a static concurrent assertion is monitored directly in a static
  // checker and queued (pending procedural assertion queue) in a procedural
  // checker.
  EXPECT_EQ(TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticConcurrentAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, StaticDeferredAssertionTreatment) {
  // §17.3: a static deferred assertion is monitored on expression change in a
  // static checker and queued (pending deferred assertion report) in a
  // procedural checker.
  EXPECT_EQ(TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kStatic),
            StaticAssertionTreatment::kMonitoredDirectly);
  EXPECT_EQ(
      TreatmentOfStaticDeferredAssertion(CheckerInstanceKind::kProcedural),
      StaticAssertionTreatment::kAddedToPendingQueue);
}

TEST(CheckerInstanceScheduling, NestedStaticCheckerFollowsTopLevelAncestor) {
  // §17.3: a static checker statically instantiated inside another checker has
  // its static assertions follow the top-level ancestor's instance kind; an
  // un-nested checker keeps its own kind.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kProcedural);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/true,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kStatic);
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kStatic,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kProcedural),
            CheckerInstanceKind::kStatic);
  // Edge: when not nested, the instance's own kind is returned regardless of
  // any ancestor kind, so a procedural own kind is preserved.
  EXPECT_EQ(EffectiveKindForStaticAssertions(
                /*own_kind=*/CheckerInstanceKind::kProcedural,
                /*nested_inside_another_checker=*/false,
                /*top_level_ancestor_kind=*/CheckerInstanceKind::kStatic),
            CheckerInstanceKind::kProcedural);
}

// §17.2 lets a checker be declared in a package, and §17.3's
// ps_checker_identifier instantiates it by the package's name, `p::chk`, or
// by a name an import made visible (§26.3), here past a package q whose
// wildcard import and explicit import of another name hold no checker. Each
// instance fails at 15 and 25 of the five posedges. Both were reported as
// unknown modules.
TEST(CheckerInstanceScheduling, ACheckerDeclaredInAPackageIsInstantiated) {
  SimFixture f;
  auto* c_pass = RunAndFindVar(
      "package q;\n"
      "  parameter int unused = 0;\n"
      "endpackage\n"
      "package p;\n"
      "  checker chk(logic a, logic clk);\n"
      "    int pass = 0, fail = 0;\n"
      "    a1: assert property (@(posedge clk) a) pass++; else fail++;\n"
      "  endchecker\n"
      "endpackage\n"
      "module top;\n"
      "  import q::unused;\n"
      "  import q::*;\n"
      "  import p::*;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  p::chk c(a, clk);\n"
      "  chk c2(a, clk);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(c_pass, nullptr);
  EXPECT_EQ(c_pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c2.pass")->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("c2.fail")->value.ToUint64(), 2u);
}

// §17.2 and §17.9: a checker formal whose actual, or default where the
// instance binds none, is an elaboration-time constant is that constant in
// the checker, so a conditional generate tests it (§27.5). c binds lvl to 1
// and takes clevel's default cover_all, keeping the cover; d binds lvl by
// name to 0 and e binds clevel to cover_none, dropping it. The condition was
// reported not constant and every instance dropped the block.
TEST(CheckerInstanceScheduling, AConstantFormalSelectsAGenerateBlock) {
  SimFixture f;
  auto* c_cov = RunAndFindVar(
      "typedef enum { cover_none, cover_all } coverage_level;\n"
      "checker chk(logic clk, int lvl, coverage_level clevel = cover_all);\n"
      "  int cov = 0;\n"
      "  if (lvl != 0 && clevel != cover_none) begin : cover_b\n"
      "    c1: cover property (@(posedge clk) 1) cov++;\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk, 1);\n"
      "  chk d(.clk(clk), .lvl(0));\n"
      "  chk e(clk, 2, cover_none);\n"
      "  initial #7 $finish;\n"
      "endmodule\n",
      f, "c.cov");
  ASSERT_NE(c_cov, nullptr);
  EXPECT_EQ(c_cov->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("d.cov")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("e.cov")->value.ToUint64(), 0u);
}

}  // namespace
