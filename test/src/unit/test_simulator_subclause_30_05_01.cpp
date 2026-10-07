#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "fixture_specify_path_decl.h"
#include "helpers_preprocess_and_get.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelaySim, SixDelayPathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SpecifyPathDelaySim, RuntimePathDelayTwelveDelays) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "in";
  pd.dst_port = "out";
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) {
    pd.delays[i] = static_cast<uint64_t>(i) + 1;
  }
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("in", "out"));
  auto& delays = mgr.GetPathDelays();
  ASSERT_EQ(delays.size(), 1u);
  EXPECT_EQ(delays[0].delay_count, 12u);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(delays[0].delays[i], static_cast<uint64_t>(i) + 1);
  }
}

TEST(SpecifyPathDelaySim, RuntimePathDelayTwoDelays) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delays[0] = 10;
  pd.delays[1] = 12;
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("a", "b"));
  EXPECT_FALSE(mgr.HasPathDelay("b", "a"));
  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 10u);
  EXPECT_EQ(mgr.GetPathDelay("x", "y"), 0u);
  EXPECT_EQ(mgr.PathDelayCount(), 1u);
}

TEST(SpecifyPathDelaySim, SingleValueIgnoresDelayMode) {
  for (auto mode : {DelayMode::kMin, DelayMode::kTyp, DelayMode::kMax}) {
    SimFixture f;
    f.ctx.SetDelayMode(mode);
    auto* e = ParseExprFrom("7", f);
    ASSERT_NE(e, nullptr);
    auto val = EvalExpr(e, f.ctx, f.arena, 32);
    EXPECT_EQ(val.ToUint64(), 7u);
  }
}

TEST(SpecifyPathDelaySim, ClampPathDelayNegativeIsZero) {
  EXPECT_EQ(ClampPathDelay(-1), 0u);
  EXPECT_EQ(ClampPathDelay(-5), 0u);
  EXPECT_EQ(ClampPathDelay(INT64_MIN), 0u);
}

TEST(SpecifyPathDelaySim, ClampPathDelayZeroPasses) {
  EXPECT_EQ(ClampPathDelay(0), 0u);
}

TEST(SpecifyPathDelaySim, ClampPathDelayPositivePasses) {
  EXPECT_EQ(ClampPathDelay(1), 1u);
  EXPECT_EQ(ClampPathDelay(42), 42u);
  EXPECT_EQ(ClampPathDelay(INT64_MAX), static_cast<uint64_t>(INT64_MAX));
}

// --- §30.5 dependency: a path delay may be a specparam, not just a literal.
// Each claim is re-observed with the delay expressions built from real
// specparam declarations and driven through parse+elaborate+lower. -----------

TEST(SpecifyPathDelayFromSource, SpecparamDelaysDistributeAcrossTransitions) {
  SimFixture f;
  auto c = ElaboratePathDecl(
      "input a, output b",
      "    specparam tr = 3, tf = 5;\n    (a => b) = (tr, tf);", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  ASSERT_EQ(c.decl->delays.size(), 2u);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 2u);
  EXPECT_EQ(pd.delays[0], 3u);  // rise from specparam tr
  EXPECT_EQ(pd.delays[1], 5u);  // fall from specparam tf
  EXPECT_EQ(pd.delays[2], 3u);
  EXPECT_EQ(pd.delays[4], 5u);
}

TEST(SpecifyPathDelayFromSource, SpecparamNegativeDelayBecomesZero) {
  SimFixture f;
  auto c = ElaboratePathDecl("input a, output b",
                             "    specparam d = -5;\n    (a => b) = d;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 0u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, SpecparamMinTypMaxSelectsTypical) {
  SimFixture f;
  auto c = ElaboratePathDecl(
      "input a, output b",
      "    specparam lo = 1, mid = 2, hi = 3;\n    (a => b) = lo:mid:hi;", f);
  ASSERT_NE(c.decl, nullptr);
  ASSERT_NE(c.design, nullptr);
  LowerAndRun(c.design, f);
  PathDelay pd = BuildPathDelayFromDecl(*c.decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 2u) << "slot " << i;
}

// --- §30.5.1 Table 30-2: how many delays are listed decides the transition
// association. Each input form (1/2/3/6/12) is built from real source. -------

TEST(SpecifyPathDelayFromSource, OneDelayFillsAllBasicTransitions) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = 7;", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 1u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 1u);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, TwoDelaysSplitRiseAndFall) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (3, 5);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 2u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 2u);
  // 0->1, 0->z, z->1 take the rise delay; 1->0, 1->z, z->0 take the fall delay.
  EXPECT_EQ(pd.delays[0], 3u);
  EXPECT_EQ(pd.delays[1], 5u);
  EXPECT_EQ(pd.delays[2], 3u);
  EXPECT_EQ(pd.delays[3], 3u);
  EXPECT_EQ(pd.delays[4], 5u);
  EXPECT_EQ(pd.delays[5], 5u);
}

TEST(SpecifyPathDelayFromSource, ThreeDelaysAddZColumn) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (2, 4, 6);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 3u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 3u);
  EXPECT_EQ(pd.delays[0], 2u);  // 0->1 rise
  EXPECT_EQ(pd.delays[1], 4u);  // 1->0 fall
  EXPECT_EQ(pd.delays[2], 6u);  // 0->z uses tz
  EXPECT_EQ(pd.delays[3], 2u);  // z->1 uses rise
  EXPECT_EQ(pd.delays[4], 6u);  // 1->z uses tz
  EXPECT_EQ(pd.delays[5], 4u);  // z->0 uses fall
}

TEST(SpecifyPathDelayFromSource, SixDelaysKeepBasicSlots) {
  SimFixture f;
  const auto* decl =
      FirstPathDecl("    (a => b) = (10, 11, 12, 13, 14, 15);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 6u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 6u);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(10 + i)) << "slot " << i;
  }
}

TEST(SpecifyPathDelayFromSource, TwelveDelaysAreCarriedVerbatim) {
  SimFixture f;
  const auto* decl = FirstPathDecl(
      "    (a => b) = (20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31);", f);
  ASSERT_NE(decl, nullptr);
  ASSERT_EQ(decl->delays.size(), 12u);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delay_count, 12u);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(20 + i)) << "slot " << i;
  }
}

// --- §30.5.1: a delay expression that evaluates negative is treated as zero,
// observed on values produced by real path_delay_expressions. ----------------

TEST(SpecifyPathDelayFromSource, NegativeSingleDelayBecomesZero) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = -5;", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 0u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, NegativeAndPositiveMixClampsOnlyNegative) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = (-3, 5);", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  EXPECT_EQ(pd.delays[0], 0u);  // clamped rise
  EXPECT_EQ(pd.delays[1], 5u);  // fall unchanged
  EXPECT_EQ(pd.delays[2], 0u);
  EXPECT_EQ(pd.delays[4], 5u);
}

// --- §30.5.1: a single value is the typical delay; a min:typ:max triple picks
// a member per the delay mode. Built from real source, distributed to slots. --

TEST(SpecifyPathDelayFromSource, MinTypMaxSelectsTypicalByDefault) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = 1:2:3;", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 2u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, MinTypMaxSelectsMinimumInMinMode) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMin);
  const auto* decl = FirstPathDecl("    (a => b) = 1:2:3;", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 1u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, MinTypMaxSelectsMaximumInMaxMode) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMax);
  const auto* decl = FirstPathDecl("    (a => b) = 1:2:3;", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 3u) << "slot " << i;
}

TEST(SpecifyPathDelayFromSource, NegativeTypicalMemberClampsToZero) {
  SimFixture f;
  const auto* decl = FirstPathDecl("    (a => b) = -9:-4:-1;", f);
  ASSERT_NE(decl, nullptr);
  PathDelay pd = BuildPathDelayFromDecl(*decl, f.ctx, f.arena);
  for (int i = 0; i < 6; ++i) EXPECT_EQ(pd.delays[i], 0u) << "slot " << i;
}

// A buffer whose one path takes its delay from `delay`, driven 0 at 0, 1 at 10
// and 0 at 20 under `timescale 1ns / 1ps, printing each change of its output
// after 0. The output's first change, from x to 0, crosses the path as the
// later ones do, so it too lands one path delay after its source's.
std::string BufferWithPathDelay(const std::string& specparam,
                                const std::string& delay) {
  return "`timescale 1ns / 1ps\n"
         "module mybuf(input a, output y);\n"
         "  assign y = a;\n"
         "  specify\n" +
         specparam + "    (a => y) = " + delay +
         ";\n"
         "  endspecify\n"
         "endmodule\n"
         "module t;\n"
         "  logic a;\n"
         "  wire y;\n"
         "  mybuf u(.a(a), .y(y));\n"
         "  always @(y) if ($realtime > 0) $display(\"t=%g y=%b\", $realtime,"
         " y);\n"
         "  initial begin\n"
         "    a = 0;\n"
         "    #10 a = 1;\n"
         "    #10 a = 0;\n"
         "  end\n"
         "endmodule\n";
}

// §30.5 with §22.7 (printed page 716): the time unit is what time values, the
// simulation time and delays among them, are measured in, so a path delay is a
// count of the declaring module's unit, and a real one keeps what its fraction
// the module's precision holds (§3.14.1). A specparam holding 2.5 -- a real, as
// §6.20.5 (printed page 129) gives a specparam with no range its value's range
// -- delays each transition by 2.5 ns under `timescale 1ns / 1ps. The delay was
// read as 3 ticks of the 1 ps precision: the specparam stored the rounded
// integer and the path took it unscaled.
TEST(SpecifyPathDelayFromSource, RealSpecparamDelayCountsTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                BufferWithPathDelay("    specparam tr = 2.5;\n", "tr"), f),
            "t=2.5 y=0\nt=12.5 y=1\nt=22.5 y=0\n");
}

// The same for a literal: an integer path delay of 3 is 3 ns, and a real 2.5
// written in the path itself is 2.5 ns.
TEST(SpecifyPathDelayFromSource, LiteralPathDelaysCountTheModuleUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(BufferWithPathDelay("", "3"), f),
            "t=3 y=0\nt=13 y=1\nt=23 y=0\n");
  SimFixture g;
  EXPECT_EQ(PreprocessAndCapture(BufferWithPathDelay("", "2.5"), g),
            "t=2.5 y=0\nt=12.5 y=1\nt=22.5 y=0\n");
}

// §22.7: the unit is the declaring module's, not the top's, so a path of 2 in
// a module under `timescale 1us / 1ns delays by 2000 of a 1 ns top's units.
TEST(SpecifyPathDelayFromSource, PathDelayCountsItsOwnModulesUnit) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1us / 1ns\n"
                                 "module slow_cell(input a, output y);\n"
                                 "  assign y = a;\n"
                                 "  specify\n"
                                 "    (a => y) = 2;\n"
                                 "  endspecify\n"
                                 "endmodule\n"
                                 "`timescale 1ns / 1ns\n"
                                 "module t;\n"
                                 "  logic a;\n"
                                 "  wire y;\n"
                                 "  slow_cell c(a, y);\n"
                                 "  always @(y) if ($time > 0)\n"
                                 "    $display(\"y=%b %0d\", y, $time);\n"
                                 "  initial #10 a = 1;\n"
                                 "endmodule\n",
                                 f),
            "y=1 2010\n");
}

}  // namespace
