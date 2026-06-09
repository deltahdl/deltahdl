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

TEST(SpecifyPathDelaySim, ExpandOneDelayFillsAllBasicSlots) {

  PathDelay pd;
  pd.delay_count = 1;
  pd.delays[0] = 7;
  ExpandTransitionDelays(pd);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(pd.delays[i], 7u) << "slot " << i;
  }
}

TEST(SpecifyPathDelaySim, ExpandTwoDelaysDistributesRiseAndFall) {

  PathDelay pd;
  pd.delay_count = 2;
  pd.delays[0] = 3;
  pd.delays[1] = 5;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[0], 3u);
  EXPECT_EQ(pd.delays[1], 5u);
  EXPECT_EQ(pd.delays[2], 3u);
  EXPECT_EQ(pd.delays[3], 3u);
  EXPECT_EQ(pd.delays[4], 5u);
  EXPECT_EQ(pd.delays[5], 5u);
}

TEST(SpecifyPathDelaySim, ExpandThreeDelaysAddsZColumn) {

  PathDelay pd;
  pd.delay_count = 3;
  pd.delays[0] = 2;
  pd.delays[1] = 4;
  pd.delays[2] = 6;
  ExpandTransitionDelays(pd);
  EXPECT_EQ(pd.delays[0], 2u);
  EXPECT_EQ(pd.delays[1], 4u);
  EXPECT_EQ(pd.delays[2], 6u);
  EXPECT_EQ(pd.delays[3], 2u);
  EXPECT_EQ(pd.delays[4], 6u);
  EXPECT_EQ(pd.delays[5], 4u);
}

TEST(SpecifyPathDelaySim, ExpandSixDelaysKeepsIdentityForBasicSlots) {

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

}
