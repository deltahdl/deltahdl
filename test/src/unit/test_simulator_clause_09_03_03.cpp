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

}  // namespace
