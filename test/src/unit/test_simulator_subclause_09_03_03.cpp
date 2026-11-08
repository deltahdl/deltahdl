#include <gtest/gtest.h>

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
  auto* var = RunAndFindVar(
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
      f, "r");
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
  auto* snap = RunAndFindVar(
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
      f, "snap_b");
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
  EXPECT_EQ(snap->value.ToUint64(), 0u);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

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
  EXPECT_EQ(snap_flag->value.ToUint64(), 1u);
  EXPECT_EQ(snap_x->value.ToUint64(), 0u);
  EXPECT_EQ(x->value.ToUint64(), 1u);
}

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
  EXPECT_EQ(snap_early->value.ToUint64(), 0u);
  EXPECT_EQ(snap_late->value.ToUint64(), 7u);
  EXPECT_EQ(areg->value.ToUint64(), 7u);
}

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
  EXPECT_EQ(snap_wb->value.ToUint64(), 1u);
  EXPECT_EQ(wa->value.ToUint64(), 1u);
  EXPECT_EQ(wb->value.ToUint64(), 1u);
}

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
