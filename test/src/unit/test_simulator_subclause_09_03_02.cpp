#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ParallelBlockSimulation, ForkJoinAllChildrenExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd10;\n"
      "      b = 8'd20;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(ParallelBlockSimulation, ForkJoinAnyChildrenExecute) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd7;\n"
      "      b = 8'd8;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 7u);
  EXPECT_EQ(b->value.ToUint64(), 8u);
}

TEST(ParallelBlockSimulation, EmptyForkJoin) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    fork join\n"
      "    x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ParallelBlockSimulation, ForkJoinNoneParentContinues) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    fork\n"
      "      ;\n"
      "    join_none\n"
      "    x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ParallelBlockSimulation, ForkWithBeginEndSingleProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 8'd1;\n"
      "        b = 8'd2;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}});
}

TEST(ParallelBlockSimulation, DelaysRelativeToBlockEntry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] snap_a, snap_b;\n"
      "  initial begin\n"
      "    fork\n"
      "      #5 a = 8'd1;\n"
      "      #10 b = 8'd2;\n"
      "    join\n"
      "  end\n"
      "  initial begin\n"
      "    #6 snap_a = a;\n"
      "    #6 snap_b = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"snap_a", 1u}, {"snap_b", 2u}, {"a", 1u}, {"b", 2u}});
}

TEST(ParallelBlockSimulation, BlockItemDeclInitVisibleToSpawnedProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      automatic int k = 8'd5;\n"
      "      result = k[7:0];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 5u}});
}

TEST(ParallelBlockSimulation, JoinNoneChildDelayedUntilParentBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] signal;\n"
      "  logic [7:0] capture;\n"
      "  initial begin\n"
      "    signal = 8'd0;\n"
      "    fork\n"
      "      capture = signal;\n"
      "    join_none\n"
      "    signal = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"capture", 42u}, {"signal", 42u}});
}

TEST(ParallelBlockSimulation, JoinBlocksParentUntilAllChildrenFinish) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] post_join;\n"
      "  logic [7:0] snap_mid;\n"
      "  logic [7:0] snap_after;\n"
      "  initial begin\n"
      "    post_join = 8'd0;\n"
      "    fork\n"
      "      #5 ;\n"
      "      #20 ;\n"
      "    join\n"
      "    post_join = 8'd7;\n"
      "  end\n"
      "  initial begin\n"
      "    #10 snap_mid = post_join;\n"
      "    #15 snap_after = post_join;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"snap_mid", 0u}, {"snap_after", 7u}, {"post_join", 7u}});
}

TEST(ParallelBlockSimulation, JoinAnyResumesParentOnFirstFinish) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] post_join;\n"
      "  logic [7:0] snap_early;\n"
      "  initial begin\n"
      "    post_join = 8'd0;\n"
      "    fork\n"
      "      #5 ;\n"
      "      #100 ;\n"
      "    join_any\n"
      "    post_join = 8'd9;\n"
      "  end\n"
      "  initial begin\n"
      "    #10 snap_early = post_join;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"snap_early", 9u}, {"post_join", 9u}});
}

TEST(ParallelBlockSimulation, ForkJoinNoneAllChildrenComplete) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "    join_none\n"
      "    c = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(b->value.ToUint64(), 2u);
  EXPECT_EQ(c->value.ToUint64(), 3u);
}

TEST(ParallelBlockSimulation, ForkBranchInsideAClassTaskKeepsThis) {
  auto val = RunAndGet(
      "class C;\n"
      "  int a = 11, b;\n"
      "  int seen;\n"
      "  task run();\n"
      "    fork\n"
      "      begin #2 this.a = a + 1; end\n"
      "      begin #3 b = a * 10; end\n"
      "    join\n"
      "    seen = a * 1000 + b;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.run();\n"
      "    result = h.seen;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 12120u);
}

TEST(ParallelBlockSimulation, JoinNoneBranchInsideAClassTaskKeepsThis) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v = 21;\n"
      "  int seen;\n"
      "  task run();\n"
      "    fork\n"
      "      begin #1 v = v * 2; end\n"
      "    join_none\n"
      "    #2 seen = v;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.run();\n"
      "    result = h.seen;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 42u);
}

TEST(ParallelBlockSimulation, ForkBranchSeesTheEnclosingScopesLocals) {
  auto val = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    for (int j = 1; j <= 3; ++j)\n"
      "      fork\n"
      "        automatic int k = j;\n"
      "        #k begin\n"
      "          automatic int m = j;\n"
      "          result = result + k * 10 + m;\n"
      "        end\n"
      "      join_none\n"
      "    #5;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 72u);
}

TEST(ParallelBlockSimulation, ForkBranchWritesTheMethodsLocal) {
  auto val = RunAndGet(
      "class C;\n"
      "  int seen;\n"
      "  task run();\n"
      "    int loc = 5;\n"
      "    fork\n"
      "      begin #1 loc = loc + 2; end\n"
      "    join\n"
      "    seen = loc;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.run();\n"
      "    result = h.seen;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 7u);
}

TEST(ForkSim, BranchInASubmoduleReadsAndWritesTheInstancesVariables) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  int x = 7, y;\n"
      "  initial fork\n"
      "    #1 y = x;\n"
      "  join\n"
      "endmodule\n"
      "module t;\n"
      "  m mi();\n"
      "  int r;\n"
      "  initial #2 r = mi.y;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
