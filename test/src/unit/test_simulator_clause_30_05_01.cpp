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

TEST(SpecifyPathDelaySim, TwelveDelayPathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(SpecifyPathDelaySim, MinTypMaxDelaySimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(SpecifyPathDelaySim, RuntimePathDelaySixDelays) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delay_count = 6;
  pd.delays[0] = 1;
  pd.delays[1] = 2;
  pd.delays[2] = 3;
  pd.delays[3] = 4;
  pd.delays[4] = 5;
  pd.delays[5] = 6;
  mgr.AddPathDelay(pd);

  EXPECT_TRUE(mgr.HasPathDelay("a", "b"));
  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 1u);
  EXPECT_EQ(mgr.PathDelayCount(), 1u);

  auto& delays = mgr.GetPathDelays();
  ASSERT_EQ(delays.size(), 1u);
  EXPECT_EQ(delays[0].delay_count, 6u);
  EXPECT_EQ(delays[0].delays[0], 1u);
  EXPECT_EQ(delays[0].delays[3], 4u);
  EXPECT_EQ(delays[0].delays[5], 6u);
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

TEST(SpecifyPathDelaySim, RuntimePathDelaySingleDelay) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "b";
  pd.delay_count = 1;
  pd.delays[0] = 10;
  mgr.AddPathDelay(pd);

  EXPECT_EQ(mgr.GetPathDelay("a", "b"), 10u);
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

TEST(SpecifyPathDelaySim, TwoDelayPathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = (3, 5);\n"
      "  endspecify\n"
      "  initial x = 8'd88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(SpecifyPathDelaySim, ThreeDelayPathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = (2, 3, 4);\n"
      "  endspecify\n"
      "  initial x = 8'd66;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// ===========================================================================
// §30.5.1 R1 — min:typ:max selection follows SimContext DelayMode.
// ===========================================================================

TEST(SpecifyPathDelaySim, MinTypMaxSelectsTypicalByDefault) {
  SimFixture f;
  auto* e = ParseExprFrom("1:2:3", f);
  ASSERT_NE(e, nullptr);
  ASSERT_EQ(e->kind, ExprKind::kMinTypMax);
  auto val = EvalExpr(e, f.ctx, f.arena, 32);
  EXPECT_EQ(val.ToUint64(), 2u);
}

TEST(SpecifyPathDelaySim, MinTypMaxSelectsMinimumInMinMode) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMin);
  auto* e = ParseExprFrom("1:2:3", f);
  ASSERT_NE(e, nullptr);
  auto val = EvalExpr(e, f.ctx, f.arena, 32);
  EXPECT_EQ(val.ToUint64(), 1u);
}

TEST(SpecifyPathDelaySim, MinTypMaxSelectsMaximumInMaxMode) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMax);
  auto* e = ParseExprFrom("1:2:3", f);
  ASSERT_NE(e, nullptr);
  auto val = EvalExpr(e, f.ctx, f.arena, 32);
  EXPECT_EQ(val.ToUint64(), 3u);
}

TEST(SpecifyPathDelaySim, SingleValueIgnoresDelayMode) {
  // §30.5.1: a single value represents the typical delay. The same value is
  // used regardless of the configured DelayMode because no alternatives exist.
  for (auto mode : {DelayMode::kMin, DelayMode::kTyp, DelayMode::kMax}) {
    SimFixture f;
    f.ctx.SetDelayMode(mode);
    auto* e = ParseExprFrom("7", f);
    ASSERT_NE(e, nullptr);
    auto val = EvalExpr(e, f.ctx, f.arena, 32);
    EXPECT_EQ(val.ToUint64(), 7u);
  }
}

// ===========================================================================
// §30.5.1 R2 — negative path delay values are treated as zero.
// ===========================================================================

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

TEST(SpecifyPathDelaySim, NegativePathDelaySimulatesAsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = -5;\n"
      "  endspecify\n"
      "  initial x = 8'd17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

// ===========================================================================
// §30.5.1 R3 — Table 30-2 associates N delay expressions with transitions.
// Scope: non-x transitions only; x-transition handling belongs to §30.5.2.
// Slot order in PathDelay::delays matches the 12-delay column of Table 30-2:
//   [0]=t01 [1]=t10 [2]=t0z [3]=tz1 [4]=t1z [5]=tz0.
// ===========================================================================

TEST(SpecifyPathDelaySim, ExpandOneDelayFillsAllBasicSlots) {
  // Count 1: every basic transition takes the same t value.
  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 7;
  ExpandTransitionDelays(pd);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
  }
}

TEST(SpecifyPathDelaySim, ExpandTwoDelaysDistributesRiseAndFall) {
  // Count 2: trise is used for rising/settling transitions, tfall for the
  // falling/returning ones. Table 30-2 column "2".
  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 3;  // trise
  pd.delays[1] = 5;  // tfall
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[0], 3u);  // 0->1 = trise
  EXPECT_EQ(pd.delays[1], 5u);  // 1->0 = tfall
  EXPECT_EQ(pd.delays[2], 3u);  // 0->z = trise
  EXPECT_EQ(pd.delays[3], 3u);  // z->1 = trise
  EXPECT_EQ(pd.delays[4], 5u);  // 1->z = tfall
  EXPECT_EQ(pd.delays[5], 5u);  // z->0 = tfall
}

TEST(SpecifyPathDelaySim, ExpandThreeDelaysAddsZColumn) {
  // Count 3: z-bound transitions share a dedicated tz value; the remaining
  // rising/falling transitions use trise/tfall.
  PathDelay pd;
  pd.delay_count = 3;
  pd.delays[0] = 2;  // trise
  pd.delays[1] = 4;  // tfall
  pd.delays[2] = 6;  // tz
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[0], 2u);  // 0->1 = trise
  EXPECT_EQ(pd.delays[1], 4u);  // 1->0 = tfall
  EXPECT_EQ(pd.delays[2], 6u);  // 0->z = tz
  EXPECT_EQ(pd.delays[3], 2u);  // z->1 = trise
  EXPECT_EQ(pd.delays[4], 6u);  // 1->z = tz
  EXPECT_EQ(pd.delays[5], 4u);  // z->0 = tfall
}

TEST(SpecifyPathDelaySim, ExpandSixDelaysKeepsIdentityForBasicSlots) {
  // Count 6: each transition has its own distinct value and none are shared.
  PathDelay pd;
  pd.delay_count = 6;
  pd.delays[0] = 10;
  pd.delays[1] = 11;
  pd.delays[2] = 12;
  pd.delays[3] = 13;
  pd.delays[4] = 14;
  pd.delays[5] = 15;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 11u);
  EXPECT_EQ(pd.delays[2], 12u);
  EXPECT_EQ(pd.delays[3], 13u);
  EXPECT_EQ(pd.delays[4], 14u);
  EXPECT_EQ(pd.delays[5], 15u);
}

TEST(SpecifyPathDelaySim, ExpandTwelveDelaysLeavesAllSlotsUntouched) {
  // Count 12: the 12-expression form is already fully explicit per Table 30-2;
  // expansion is a no-op across all twelve slots (including the x-transition
  // slots 6..11 which §30.5.1 does not re-specify).
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) {
    pd.delays[i] = static_cast<uint64_t>(100 + i);
  }
  ExpandTransitionDelays(pd);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.delays[i], static_cast<uint64_t>(100 + i)) << "slot " << i;
  }
}

}  // namespace
