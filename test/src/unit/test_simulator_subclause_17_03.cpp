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

// §17.2 and §17.3: a checker formal of type string carries its actual, or
// its default where the instance binds none, into the checker body, an
// action block among it, whole: c takes the fourteen-character default and
// c2 the actual. The formal read as an empty string, having no width to be
// connected at, and a default was cut to its last eight characters.
TEST(CheckerInstanceScheduling, AStringFormalCarriesItsActualOrDefault) {
  SimFixture f;
  auto* len = RunAndFindVar(
      "checker chk(logic clk, string msg = \"violation-long\");\n"
      "  int len = 0, same = 0;\n"
      "  a1: assert property (@(posedge clk) 0) else begin\n"
      "    len = msg.len();\n"
      "    same = msg == \"violation-long\" || msg == \"boom\";\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  chk c2(clk, \"boom\");\n"
      "  initial #12 $finish;\n"
      "endmodule\n",
      f, "c.len");
  ASSERT_NE(len, nullptr);
  EXPECT_EQ(len->value.ToUint64(), 14u);
  EXPECT_EQ(f.ctx.FindVariable("c.same")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c2.len")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.same")->value.ToUint64(), 1u);
}

// §17.2 and §17.3: an assertion clocked by a checker formal of type event
// waits on its actual, a named event c's module triggers at every clock edge
// and the clock signal itself for c2, so each is attempted at the ten edges
// from 5 to 50 and fails at the four where a is low. Neither was attempted:
// the formal, having no width, was never connected.
TEST(CheckerInstanceScheduling, AnEventFormalClocksTheCheckersAssertion) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic a, event clk);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@clk a) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  event ev;\n"
      "  always #5 begin clk = ~clk; -> ev; end\n"
      "  chk c(a, ev);\n"
      "  chk c2(a, clk);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("c2.pass")->value.ToUint64(), 6u);
  EXPECT_EQ(f.ctx.FindVariable("c2.fail")->value.ToUint64(), 4u);
}

// §17.3: a checker formal written as a cycle delay's bound takes its
// actual, `##n` with n bound to 2 being `##2` and `##[1:m]` with m bound to
// `$` being `##[1:$]`, in an or's operands and in a group nested in a chain
// as well. a is high at the posedge at 5 alone and b from 25, so each
// assertion holds there, and vacuously at the other four posedges. Each
// bound was read as 1, failing at 15.
TEST(CheckerInstanceScheduling, AFormalBoundsACycleDelay) {
  SimFixture f;
  auto* p1 = RunAndFindVar(
      "checker chk(logic a, b, int n, untyped m, logic clk);\n"
      "  int p1 = 0, p2 = 0, p3 = 0, p4 = 0;\n"
      "  a1: assert property (@(posedge clk) a |-> ##n b) p1++;\n"
      "  a2: assert property (@(posedge clk) a |-> ##[1:m] b) p2++;\n"
      "  a3: assert property (@(posedge clk) a |-> (##n b or ##[1:m] b))\n"
      "    p3++;\n"
      "  a4: assert property (@(posedge clk)\n"
      "    a |-> 1'b1 ##0 (##n b or 1'b0)) p4++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 0, b = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(a, b, 2, $, clk);\n"
      "  initial begin #2 a = 1; #10 a = 0; #10 b = 1; #30 $finish; end\n"
      "endmodule\n",
      f, "c.p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(p1->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p2")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p3")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.p4")->value.ToUint64(), 5u);
}

}  // namespace
