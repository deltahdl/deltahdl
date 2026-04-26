#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

// §4.9.4 atom: the update is scheduled as an NBA update event — the callback
// goes into `Region::kNBA`, which drains after the Active region.
// `ScheduleNonblockingAssign` calls `ScheduleEvent(..., Region::kNBA, event)`
// so the LHS write is not visible to subsequent Active-region statements.
// Observed by `dst <= 8'd7; snap = dst;` inside the same initial — the
// blocking `snap = dst;` runs in Active, before the NBA region, so it captures
// the prior `dst` (0). A misroute of the update into the Active region (or
// any region before NBA) would leave `snap == 7`.
TEST(NonblockingAssignSchedulingSim, SchedulesUpdateInNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, snap;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    dst <= 8'd7;\n"
      "    snap = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
}

// §4.9.4 atoms: NBA always computes the updated value, and when the delay is
// zero the event is placed in the current time step.
// `ExecNonblockingAssignImpl` evaluates the RHS via `EvalRhsWithStructContext`
// and `ScheduleNonblockingAssign` schedules at
// `current_time + SimTime{delay_ticks}`, with `delay_ticks == 0` resolving to
// the current time. Observed by a bare `dst <= 8'd5;` at t=0 with no other
// events — after `Run`, `dst` is 5 (so the eager evaluate-and-schedule path
// fired) and `CurrentTime` is still 0 (so the placement is in the current
// step). A no-op NBA path would leave `dst == 0`; a future schedule would
// advance the clock past 0.
TEST(NonblockingAssignSchedulingSim, ZeroDelaySchedulesInCurrentTimestep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    dst <= 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// §4.9.4 atom: when the delay is nonzero, the NBA event is scheduled as a
// future event. `ExecNonblockingAssignImpl` reads `stmt->delay`, evaluates it,
// and `ScheduleNonblockingAssign` adds it to the current time. Observed by
// `dst <= #10 8'd99;` from t=0 with a parallel `#5 mid = dst;` — at t=5 the
// NBA has not yet fired, so `mid` captures the pre-NBA `dst` (0); after the
// scheduler advances to t=10 and drains its NBA region, `dst` commits to 99.
// A current-step schedule would leave `mid == 99`.
TEST(NonblockingAssignSchedulingSim, NonzeroDelaySchedulesAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, mid;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    mid = 8'd0;\n"
      "    dst <= #10 8'd99;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 mid = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

// §4.9.4 atom: the values in effect when the update is placed in the event
// region are used to compute the right-hand value — the RHS is evaluated at
// statement-execution time, not at NBA-fire time. `ExecNonblockingAssignImpl`
// calls `EvalRhsWithStructContext` and captures the result by value into the
// NBA callback. Observed by `dst <= src;` followed immediately by `src = 99;`
// inside the same initial — `src` is 5 when the NBA is scheduled, so `dst`
// must commit to 5, not 99. A callback that re-read `src` at fire time would
// yield 99.
TEST(NonblockingAssignSchedulingSim, RhsUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = 8'd0;\n"
      "    dst <= src;\n"
      "    src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
}

// §4.9.4 atom: the values in effect when the update is placed in the event
// region are used to compute the left-hand target — the LHS index is
// resolved at schedule time, not at fire time. For `mem[idx] <= ...`,
// `ScheduleNonblockingAssign` evaluates `lhs->index` via `EvalExpr` and
// captures the resolved index into the NBA callback. Observed by
// `mem[idx] <= 8'hCC;` followed by `idx = 1;` — the NBA must write to
// `mem[0]` (the index in effect at schedule time), leaving `mem[1]`
// untouched. A fire-time index lookup would write to `mem[1]`.
TEST(NonblockingAssignSchedulingSim, LhsTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] <= 8'hCC;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0xCCu);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0u);
}

// §4.9.4 atom (edge case): for a packed-vector bit-select LHS, the schedule-
// time evaluation rule still applies — `ScheduleNonblockingAssign` takes the
// `is_select && !elem` branch (no per-element variable exists for a packed
// vector), evaluates `lhs->index` via `EvalExpr` at schedule time, and
// captures the resolved bit position into a bit-write callback. Observed by
// `dst[idx] <= 1'b1;` followed by `idx = 7;` — the NBA must set bit 0 (the
// index in effect at schedule time), not bit 7. A fire-time index lookup
// would set bit 7 instead, leaving bit 0 clear.
TEST(NonblockingAssignSchedulingSim, BitSelectLhsUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  int idx;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    idx = 0;\n"
      "    dst[idx] <= 1'b1;\n"
      "    idx = 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 0x01u);
}
