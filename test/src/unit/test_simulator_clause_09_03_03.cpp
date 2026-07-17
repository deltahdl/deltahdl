#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockStartFinishSimulation, ControlPassesOutAfterLastStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 8'd1;\n"
      "    end\n"
      "    b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}});
}

TEST(BlockStartFinishSimulation, NestedForkJoin) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        fork\n"
      "          a = 8'd10;\n"
      "          b = 8'd20;\n"
      "        join\n"
      "      end\n"
      "      c = 8'd30;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}, {"c", 30u}});
}

TEST(BlockStartFinishSimulation, NestedSeqBlockExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    r = 8'd1;\n"
      "    begin\n"
      "      r = r + 8'd1;\n"
      "    end\n"
      "    begin\n"
      "      r = r + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(BlockStartFinishSimulation, ForkJoinFinishesBeforeNextStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "    join\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

TEST(BlockStartFinishSimulation, ForkJoinAnyFinishesBeforeNextStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, done;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd5;\n"
      "      #10 ;\n"
      "    join_any\n"
      "    done = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* done = f.ctx.FindVariable("done");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(done, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 5u);
  EXPECT_EQ(done->value.ToUint64(), 1u);
}

TEST(BlockStartFinishSimulation, ParallelBlockChildrenShareStartTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, snap_b;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 8'd1;\n"
      "      #10 b = 8'd2;\n"
      "    join\n"
      "  end\n"
      "  initial begin\n"
      "    #15 snap_b = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap = f.ctx.FindVariable("snap_b");
  ASSERT_NE(snap, nullptr);
  EXPECT_EQ(snap->value.ToUint64(), 2u);
}

TEST(BlockStartFinishSimulation, SeqBlockFinishTimeAtLastStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    begin\n"
      "      #5 x = 8'd1;\n"
      "      #5 x = 8'd2;\n"
      "    end\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}, {"y", 2u}});
}

TEST(BlockStartFinishSimulation, DeeplyNestedSeqBlocksFinishBeforeContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    r = 8'd1;\n"
      "    begin\n"
      "      begin\n"
      "        begin\n"
      "          r = r + 8'd1;\n"
      "        end\n"
      "        r = r + 8'd1;\n"
      "      end\n"
      "      r = r + 8'd1;\n"
      "    end\n"
      "    r = r + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 5u}});
}

// A parallel block's finish time (with join) is the moment its last
// time-ordered statement completes; control must not reach the statement
// after the block until that time. A concurrent process sampling before the
// finish time must observe that the post-join statement has not yet run.
TEST(BlockStartFinishSimulation, ForkJoinNextStatementWaitsForFinishTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] flag, snap;\n"
      "  initial begin\n"
      "    flag = 8'd0;\n"
      "    fork\n"
      "      #10 ;\n"
      "      #20 ;\n"
      "    join\n"
      "    flag = 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #15 snap = flag;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap = f.ctx.FindVariable("snap");
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(snap, nullptr);
  ASSERT_NE(flag, nullptr);
  // At t=15 the join has not finished (longest child completes at t=20), so
  // the statement following the block has not run yet.
  EXPECT_EQ(snap->value.ToUint64(), 0u);
  // The post-join statement runs once the finish time (t=20) is reached.
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

// A fork...join_none block's finish time equals its start time (Table 9-1, see
// 9.3.2): the parent continues concurrently with the spawned children. The
// §9.3.3 gating rule therefore lets execution reach the statement following the
// block at the same simulation time as the fork, before the (delayed) children
// have finished. A concurrent process sampling shortly after start must observe
// that the post-join_none statement has already run while a delayed child has
// not yet completed.
TEST(BlockStartFinishSimulation,
     ForkJoinNoneContinuesImmediatelyBeforeChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] flag, x, snap_flag, snap_x;\n"
      "  initial begin\n"
      "    flag = 8'd0;\n"
      "    fork\n"
      "      #10 x = 8'd1;\n"
      "      #20 ;\n"
      "    join_none\n"
      "    flag = 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 snap_flag = flag;\n"
      "    snap_x = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap_flag = f.ctx.FindVariable("snap_flag");
  auto* snap_x = f.ctx.FindVariable("snap_x");
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(snap_flag, nullptr);
  ASSERT_NE(snap_x, nullptr);
  ASSERT_NE(x, nullptr);
  // join_none finishes immediately, so the post-block statement runs at t=0 and
  // the flag is already set when the observer samples at t=5.
  EXPECT_EQ(snap_flag->value.ToUint64(), 1u);
  // The children keep running concurrently: the #10 child has not run at t=5.
  EXPECT_EQ(snap_x->value.ToUint64(), 0u);
  // Once its delay elapses the background child does complete.
  EXPECT_EQ(x->value.ToUint64(), 1u);
}

// "Joining of events": a fork whose children are event controls (rather than
// delays) finishes only once every child's event has fired, in whatever order
// the events happen to occur. The §9.3.3 gating rule holds the statement after
// the join until that finish time. Two named events (see 15.5 / 9.4.2) are
// triggered at t=10 and t=20 by a separate process; the post-join assignment
// must not take effect after only the first event, and must take effect once
// the second (later) event completes the block.
TEST(BlockStartFinishSimulation, ForkJoinsSeparateEventsBeforeNextStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] areg, breg, snap_early, snap_late;\n"
      "  event Aevent, Bevent;\n"
      "  initial begin\n"
      "    areg = 8'd0;\n"
      "    breg = 8'd7;\n"
      "    fork\n"
      "      @(Aevent);\n"
      "      @(Bevent);\n"
      "    join\n"
      "    areg = breg;\n"
      "  end\n"
      "  initial begin\n"
      "    #10 -> Aevent;\n"
      "    #10 -> Bevent;\n"
      "  end\n"
      "  initial begin\n"
      "    #15 snap_early = areg;\n"
      "    #10 snap_late = areg;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap_early = f.ctx.FindVariable("snap_early");
  auto* snap_late = f.ctx.FindVariable("snap_late");
  auto* areg = f.ctx.FindVariable("areg");
  ASSERT_NE(snap_early, nullptr);
  ASSERT_NE(snap_late, nullptr);
  ASSERT_NE(areg, nullptr);
  // At t=15 only Aevent has fired; the join has not finished, so the post-join
  // assignment has not run.
  EXPECT_EQ(snap_early->value.ToUint64(), 0u);
  // By t=25 both events have fired (finish time t=20), so the assignment ran.
  EXPECT_EQ(snap_late->value.ToUint64(), 7u);
  EXPECT_EQ(areg->value.ToUint64(), 7u);
}

// Sequential and parallel blocks can be embedded within each other. When two
// begin-end blocks are the children of a fork, they execute in parallel rather
// than one-after-another: each block starts on its own event guard and its
// internal timeline overlaps the other's. Both guards fire at t=5, then each
// block waits #10 and assigns at t=15. Were the blocks serialized, the second
// block would not start until the first finished (t=15) and would assign only
// at t=25; an observer at t=20 seeing the second block's write proves the two
// embedded sequential blocks ran concurrently.
TEST(BlockStartFinishSimulation, EmbeddedSeqBlocksInForkRunInParallel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wa, wb, snap_wb;\n"
      "  event enable_a, enable_b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        @(enable_a);\n"
      "        #10 wa = 8'd1;\n"
      "      end\n"
      "      begin\n"
      "        @(enable_b);\n"
      "        #10 wb = 8'd1;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> enable_a;\n"
      "    -> enable_b;\n"
      "  end\n"
      "  initial begin\n"
      "    #20 snap_wb = wb;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap_wb = f.ctx.FindVariable("snap_wb");
  auto* wa = f.ctx.FindVariable("wa");
  auto* wb = f.ctx.FindVariable("wb");
  ASSERT_NE(snap_wb, nullptr);
  ASSERT_NE(wa, nullptr);
  ASSERT_NE(wb, nullptr);
  // Second block's write is visible at t=20, so it did not wait for the first
  // block to finish: the two embedded sequential blocks executed in parallel.
  EXPECT_EQ(snap_wb->value.ToUint64(), 1u);
  EXPECT_EQ(wa->value.ToUint64(), 1u);
  EXPECT_EQ(wb->value.ToUint64(), 1u);
}

// An empty sequential block has no statements, so its finish time equals its
// start time and control passes immediately to the following statement.
TEST(BlockStartFinishSimulation, EmptySeqBlockFinishesImmediately) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] done;\n"
      "  initial begin\n"
      "    begin\n"
      "    end\n"
      "    done = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"done", 7u}});
}

}  // namespace
