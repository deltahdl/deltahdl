#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

using namespace delta;

namespace {

TEST(DisableStatementExecution, DisableReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDisable;
  stmt->expr = MakeId(f.arena, "myblock");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(DisableStatementExecution, SelfDisableSkipsRemainingStatements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin : blk\n"
      "    a = 8'd1;\n"
      "    disable blk;\n"
      "    b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 0u}});
}

TEST(DisableStatementExecution, ExecutionResumesAfterDisabledBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      x = 8'd10;\n"
      "      disable inner;\n"
      "      x = 8'd99;\n"
      "    end\n"
      "    y = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}, {"y", 20u}});
}

TEST(DisableStatementExecution, DisableBlockFromOtherProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin : target\n"
      "    #10;\n"
      "    x = 8'd99;\n"
      "  end\n"
      "  initial begin\n"
      "    disable target;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableStatementExecution, DisableNonExecutingBlockHasNoEffect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin : done_early\n"
      "    x = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    #10;\n"
      "    disable done_early;\n"
      "    y = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 7u}});
}

TEST(DisableStatementExecution, DisableTerminatesTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task;\n"
      "    #10;\n"
      "    x = 8'd99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task;\n"
      "    join_none\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableStatementExecution, ExecutionResumesAfterTaskEnablingStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  task slow_task;\n"
      "    #100;\n"
      "    x = 8'd99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      slow_task;\n"
      "    join_none\n"
      "    disable slow_task;\n"
      "    y = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}, {"y", 1u}});
}

TEST(DisableStatementExecution, DisableTerminatesNestedActivities) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin : outer\n"
      "    fork\n"
      "      begin\n"
      "        #10;\n"
      "        x = 8'd42;\n"
      "      end\n"
      "    join_none\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableStatementExecution, DisableNestedTaskChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task inner_task;\n"
      "    #10;\n"
      "    x = 8'd42;\n"
      "  endtask\n"
      "  task outer_task;\n"
      "    inner_task;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      outer_task;\n"
      "    join_none\n"
      "    disable outer_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableStatementExecution, DisableAllActivationsOfTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  task my_task(output logic [7:0] result);\n"
      "    #10;\n"
      "    result = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task(a);\n"
      "      my_task(b);\n"
      "    join_none\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0u}, {"b", 0u}});
}

TEST(DisableStatementExecution, DisableAsForwardGoto) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin : block_name\n"
      "    a = 8'd1;\n"
      "    if (a == 1)\n"
      "      disable block_name;\n"
      "    b = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 0u}, {"c", 1u}});
}

TEST(DisableStatementExecution, DisableAsContinueInLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] count;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    for (int i = 0; i < 4; i = i + 1) begin : inner\n"
      "      if (i == 2) disable inner;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);

  LowerRunAndCheck(f, design, {{"count", 3u}});
}

TEST(DisableStatementExecution, DisableAsBreakFromLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] count;\n"
      "  initial begin : outer\n"
      "    count = 8'd0;\n"
      "    for (int i = 0; i < 10; i = i + 1) begin\n"
      "      if (i == 3) disable outer;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);

  LowerRunAndCheck(f, design, {{"count", 3u}});
}

TEST(DisableStatementExecution, TaskDisablesItself) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task proc_a;\n"
      "    x = 8'd1;\n"
      "    if (x == 1)\n"
      "      disable proc_a;\n"
      "    x = 8'd99;\n"
      "  endtask\n"
      "  initial proc_a;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(DisableStatementExecution, DisableAutomaticTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  task automatic my_task(output logic [7:0] result);\n"
      "    #10;\n"
      "    result = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task(a);\n"
      "      my_task(b);\n"
      "    join_none\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0u}, {"b", 0u}});
}

TEST(DisableStatementExecution, DisableTaskWithOutputArgumentDoesNotCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task(output logic [7:0] result);\n"
      "    #10;\n"
      "    result = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task(x);\n"
      "    join_none\n"
      "    #5;\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST(DisableStatementExecution, DisableTaskWithPendingNbaDoesNotCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task;\n"
      "    #10;\n"
      "    x <= 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task;\n"
      "    join_none\n"
      "    #10;\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST(DisableStatementExecution, DisableTaskWithProceduralAssignDoesNotCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task;\n"
      "    assign x = 8'd42;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task;\n"
      "    join_none\n"
      "    #5;\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST(DisableStatementExecution, DisableTaskWithInoutArgumentDoesNotCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task(inout logic [7:0] result);\n"
      "    #10;\n"
      "    result = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task(x);\n"
      "    join_none\n"
      "    #5;\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST(DisableStatementExecution, DisableTaskWithForceDoesNotCrash) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task my_task;\n"
      "    force x = 8'd42;\n"
      "    #10;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      my_task;\n"
      "    join_none\n"
      "    #5;\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

void RunRandseqDisableTrial(SimFixture& f, std::string_view rules) {
  std::string src =
      "module t;\n"
      "  logic [7:0] in_rs, after_rs, after_blk;\n"
      "  initial begin\n"
      "    begin : blk\n"
      "      randsequence(main)\n" +
      std::string(rules) +
      "      endsequence\n"
      "      after_rs = 8'd51;\n"
      "    end\n"
      "    after_blk = 8'd93;\n"
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design,
                   {{"in_rs", 37u}, {"after_rs", 0u}, {"after_blk", 93u}});
}

TEST(DisableStatementExecution,
     DisableInARandsequenceProductionCodeBlockTerminatesTheBlock) {
  SimFixture f;
  RunRandseqDisableTrial(f,
                         "        main : { in_rs = 8'd37; disable blk; };\n");
}

TEST(DisableStatementExecution,
     DisableInARandsequenceWeightCodeBlockTerminatesTheBlock) {
  SimFixture f;
  RunRandseqDisableTrial(f,
                         "        main : alt := 5 { disable blk; };\n"
                         "        alt : { in_rs = 8'd37; };\n");
}

TEST(DisableStatementExecution,
     DisableInAClassFunctionOfItsLoopBodyBlockActsAsContinue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  function void cont;\n"
                       "    int sum = 0, i;\n"
                       "    for (i = 0; i < 10; i = i + 1) begin : inner\n"
                       "      if (i == 1) disable inner;\n"
                       "      sum = sum + i + 2;\n"
                       "    end\n"
                       "    $display(\"cont sum=%0d i=%0d\", sum, i);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  C h = new;\n"
                       "  initial h.cont();\n"
                       "endmodule\n",
                       f),
            "cont sum=62 i=10\n");
}

TEST(DisableStatementExecution,
     DisableInAClassFunctionOfABlockAroundTheLoopActsAsBreak) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C;\n"
                 "  int sum, i;\n"
                 "  function void run(int n, int stop);\n"
                 "    begin : outer_block\n"
                 "      for (i = 0; i < n; i = i + 1) begin : inner_block\n"
                 "        if (i == 1) disable inner_block;\n"
                 "        if (i == stop) disable outer_block;\n"
                 "        sum = sum + i + 2;\n"
                 "      end\n"
                 "    end\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  C h = new;\n"
                 "  initial begin h.run(10, 3); $display(\"method sum=%0d "
                 "i=%0d\", h.sum, h.i); end\n"
                 "endmodule\n",
                 f),
      "method sum=6 i=3\n");
}

TEST(DisableStatementExecution,
     DisableFromAnotherProcessEndsTheBlockWhereItWaits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int v;\n"
                       "  initial begin\n"
                       "    begin : waiter\n"
                       "      #10 v = 1;\n"
                       "    end\n"
                       "    $display(\"other @%0d v=%0d\", $time, v);\n"
                       "  end\n"
                       "  initial #3 disable waiter;\n"
                       "endmodule\n",
                       f),
            "other @3 v=0\n");
}

TEST(DisableStatementExecution,
     DisableOfATaskFromAnotherProcessReturnsToItsCaller) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  int v;\n"
          "  task tk; #10 v = 1; endtask\n"
          "  initial begin tk(); $display(\"back @%0d v=%0d\", $time, v); end\n"
          "  initial #4 disable tk;\n"
          "endmodule\n",
          f),
      "back @4 v=0\n");
}

TEST(DisableStatementExecution,
     ForkBranchDisablingASiblingBlockLetsTheForkJoin) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  event e; int x, y;\n"
                       "  initial begin\n"
                       "    fork\n"
                       "      begin : blkA #10 x = 1; end\n"
                       "      #2 disable blkA;\n"
                       "    join\n"
                       "    $display(\"A @%0d x=%0d\", $time, x);\n"
                       "    fork\n"
                       "      begin : blkB @e y = 1; end\n"
                       "      #2 disable blkB;\n"
                       "    join\n"
                       "    $display(\"B @%0d y=%0d\", $time, y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "A @2 x=0\n"
            "B @4 y=0\n");
}

TEST(DisableStatementExecution, ResetBranchDisablesTheEventExpressionBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  event ev1, trig, reset; int acted;\n"
                       "  initial begin\n"
                       "    fork\n"
                       "      begin : event_expr\n"
                       "        @ev1;\n"
                       "        repeat (3) @trig;\n"
                       "        #4 acted = 1;\n"
                       "      end\n"
                       "      @reset disable event_expr;\n"
                       "    join\n"
                       "    $display(\"end @%0d acted=%0d\", $time, acted);\n"
                       "  end\n"
                       "  initial begin #1 -> ev1; #1 -> trig; #1 -> trig; #1 "
                       "-> trig; #1 -> reset; #5; end\n"
                       "endmodule\n",
                       f),
            "end @5 acted=0\n");
}

TEST(DisableStatementExecution, BranchDisablingItsOwnForkEndsEveryBranch) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int x;\n"
                       "  initial begin\n"
                       "    fork : f\n"
                       "      #1 disable f;\n"
                       "      #10 x = 1;\n"
                       "    join\n"
                       "    $display(\"joined @%0d x=%0d\", $time, x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "joined @1 x=0\n");
}

TEST(DisableStatementExecution,
     DisableOfANamedForkFromAnotherProcessEndsTheJoin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int x, y;\n"
                 "  initial begin\n"
                 "    fork : f\n"
                 "      #10 x = 1;\n"
                 "      #10 y = 1;\n"
                 "    join\n"
                 "    $display(\"joined @%0d x=%0d y=%0d\", $time, x, y);\n"
                 "  end\n"
                 "  initial #3 disable f;\n"
                 "endmodule\n",
                 f),
      "joined @3 x=0 y=0\n");
}

TEST(DisableStatementExecution, HierarchicalDisableOfABlockInATask) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int n, after;\n"
                 "  task counter();\n"
                 "    begin : cnt\n"
                 "      forever begin #10 n++; end\n"
                 "    end\n"
                 "    after = 1;\n"
                 "  endtask\n"
                 "  initial begin #35 disable t.counter.cnt; end\n"
                 "  initial begin\n"
                 "    counter();\n"
                 "    $display(\"n=%0d t=%0t after=%0d\", n, $time, after);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "n=3 t=35 after=1\n");
}

TEST(DisableStatementExecution, DisablingOneInstancesBlockLeavesAnothers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter int ID = 0);\n"
                       "  initial begin : blk #5 $display(\"%0d ran on\", ID); "
                       "end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(1) a();\n"
                       "  child #(2) b();\n"
                       "  initial #1 disable a.blk;\n"
                       "endmodule\n",
                       f),
            "2 ran on\n");
}

TEST(DisableStatementExecution, AModulesDisableEndsItsOwnInstancesBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter int ID = 0, STOP = 0);\n"
                       "  initial begin : blk #5 $display(\"%0d ran on\", ID); "
                       "end\n"
                       "  initial #1 if (STOP) disable blk;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(1, 1) a();\n"
                       "  child #(2, 0) b();\n"
                       "endmodule\n",
                       f),
            "2 ran on\n");
}

TEST(DisableStatementExecution, AHierarchicalDisableEndsOnlyTheBlockItReaches) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  initial begin : x\n"
                 "    begin : inner #5 $display(\"x.inner ran on\"); end\n"
                 "  end\n"
                 "  initial begin : y\n"
                 "    begin : inner #5 $display(\"y.inner ran on\"); end\n"
                 "  end\n"
                 "  initial #1 disable x.inner;\n"
                 "endmodule\n",
                 f),
      "y.inner ran on\n");
}

TEST(DisableStatementExecution, AGenerateBlocksDisableEndsTheModulesBlock) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  initial begin : blk #5 $display(\"blk ran on\"); end\n"
                 "  initial begin : other #5 $display(\"other ran on\"); "
                 "end\n"
                 "  if (1) begin : g\n"
                 "    initial #1 disable blk;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "other ran on\n");
}

TEST(DisableStatementExecution, AnUpwardNameEndsTheEnclosingInstancesBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sibm #(parameter int ID = 0);\n"
                       "  initial begin : blk #5 $display(\"%0d ran on\", ID); "
                       "end\n"
                       "endmodule\n"
                       "module low; initial #1 disable sib.blk; endmodule\n"
                       "module leaf; low w(); endmodule\n"
                       "module top;\n"
                       "  leaf l();\n"
                       "  sibm #(1) sib();\n"
                       "  sibm #(2) sib2();\n"
                       "endmodule\n",
                       f),
            "2 ran on\n");
}

TEST(DisableStatementExecution, DisablingInnerThenOuterAtOnceEndsTheProcess) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  initial begin : outer\n"
                       "    begin : inner #5 $display(\"inner ran on\"); end\n"
                       "    $display(\"outer ran on\");\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #1 disable outer.inner;\n"
                       "    disable outer;\n"
                       "  end\n"
                       "  initial #9 $display(\"done\");\n"
                       "endmodule\n",
                       f),
            "done\n");
}

TEST(DisableStatementExecution, DisablingABlockEndsItsRunningNamedBranch) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  initial begin : outer\n"
                       "    fork begin : fb #5 $display(\"fb ran on\"); end "
                       "join_none\n"
                       "    #9 $display(\"outer ran on\");\n"
                       "  end\n"
                       "  initial #1 disable outer;\n"
                       "  initial #12 $display(\"done\");\n"
                       "endmodule\n",
                       f),
            "done\n");
}

TEST(DisableStatementExecution, DisablingAnUnstartedForkBranchEndsItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter int ID = 0);\n"
                       "  initial begin\n"
                       "    fork begin : fb #5 $display(\"%0d ran on\", ID); "
                       "end join_none\n"
                       "    if (ID == 1) disable fb;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(1) a();\n"
                       "  child #(2) b();\n"
                       "endmodule\n",
                       f),
            "2 ran on\n");
}

TEST(DisableStatementExecution, DisablingALoopLabelEndsOnlyItsInstancesLoop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter int ID = 0);\n"
                       "  int a [3];\n"
                       "  initial begin\n"
                       "    lp: foreach (a[i]) begin\n"
                       "      #1;\n"
                       "      if (ID == 1 && i == 1) disable lp;\n"
                       "    end\n"
                       "    $display(\"%0d done at %0t\", ID, $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(1) a();\n"
                       "  child #(2) b();\n"
                       "endmodule\n",
                       f),
            "1 done at 2\n2 done at 3\n");
}

TEST(DisableStatementExecution, DisablingAForeachLabelInAFunctionEndsTheLoop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int a [4];\n"
                       "  int q [$] = '{7, 8, 9};\n"
                       "  function automatic int fa();\n"
                       "    int n = 0;\n"
                       "    la: foreach (a[i]) begin\n"
                       "      n++;\n"
                       "      if (i == 1) disable la;\n"
                       "    end\n"
                       "    return n + 100;\n"
                       "  endfunction\n"
                       "  function automatic int fq();\n"
                       "    int n = 0;\n"
                       "    lq: foreach (q[i]) begin\n"
                       "      n++;\n"
                       "      if (i == 0) disable lq;\n"
                       "    end\n"
                       "    return n + 200;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d\", fa(), fq());\n"
                       "endmodule\n",
                       f),
            "102 201\n");
}

TEST(DisableStatementExecution, ANearerBlockNotRunningLeavesAFartherOne) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  initial begin : y #5 $display(\"top.y ran on\"); end\n"
                 "  initial begin : outer\n"
                 "    #1;\n"
                 "    begin : x disable y; end\n"
                 "    begin : y #2; end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "top.y ran on\n");
}

TEST(DisableStatementExecution, AnInstancesBlockNotRunningLeavesTheTops) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module child;\n"
                 "  initial #1 disable y;\n"
                 "  initial #3 begin : y #1; end\n"
                 "endmodule\n"
                 "module top;\n"
                 "  child c();\n"
                 "  initial begin : y #5 $display(\"top.y ran on\"); end\n"
                 "endmodule\n",
                 f),
      "top.y ran on\n");
}

TEST(DisableStatementExecution, AnInstancesTaskNotRunningLeavesTheTopsBlock) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module child;\n"
                 "  task t; #1; endtask\n"
                 "  initial #1 disable t;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  child c();\n"
                 "  initial begin : t #5 $display(\"top.t ran on\"); end\n"
                 "endmodule\n",
                 f),
      "top.t ran on\n");
}

TEST(DisableStatementExecution, DisablingAClassTasksFinishedBlockEndsNothing) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  task run();\n"
                       "    begin : b #1; end\n"
                       "    disable b;\n"
                       "    $display(\"after at %0t\", $time);\n"
                       "  endtask\n"
                       "endclass\n"
                       "module t;\n"
                       "  C h = new;\n"
                       "  initial h.run();\n"
                       "endmodule\n",
                       f),
            "after at 1\n");
}

}  // namespace
