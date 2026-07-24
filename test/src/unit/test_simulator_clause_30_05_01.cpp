#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelaySim, SixDelayPathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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

// Parses a specify block written in real source and returns the first module
// path declaration it contains, so the §30.5.1 rules can be observed on a
// PathDelay assembled from genuine syntax (the RHS list length drives
// delay_count, and each delay is a real path_delay_expression).
const SpecifyPathDecl* FirstPathDecl(const std::string& specify_body,
                                     SimFixture& f) {
  std::string code =
      "module t;\n  specify\n" + specify_body + "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) return &si->path;
      }
    }
  }
  return nullptr;
}

// Bundles the parsed path declaration with the elaborated design so a delay
// expression that references a specparam can be observed end-to-end: the
// specparam is a real §30.5 dependency construct, and its value only becomes
// resolvable once the design is elaborated and lowered into the context.
struct ElaboratedPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  RtlirDesign* design = nullptr;
};

// Parses AND elaborates a module carrying `port_header` ports plus the given
// specify body, returning the first path declaration together with the design.
// Lowering the design seeds each specify-block specparam as a context variable,
// so EvalExpr resolves those identifiers when BuildPathDelayFromDecl runs.
ElaboratedPathDecl ElaboratePathDecl(const std::string& port_header,
                                     const std::string& specify_body,
                                     SimFixture& f) {
  std::string code = "module t(" + port_header + ");\n  specify\n" +
                     specify_body + "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  ElaboratedPathDecl out;
  out.design = elab.Elaborate(cu->modules.back()->name);
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl) {
          out.decl = &si->path;
          return out;
        }
      }
    }
  }
  return out;
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

}  // namespace
