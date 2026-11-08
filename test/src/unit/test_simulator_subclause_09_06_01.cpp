#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

using namespace delta;

namespace {

TEST(WaitForkSimulation, WaitForkNoForkReturnsDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitFork;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(WaitForkSimulation, WaitForkNoChildrenCompletesImmediately) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait fork;\n"
      "    x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(WaitForkSimulation, WaitForkBlocksUntilSingleChildCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd10;\n"
      "    join_none\n"
      "    wait fork;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 10u}});
}

TEST(WaitForkSimulation, WaitForkWaitsForLastOfStaggeredChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #5  a = 8'd1; end\n"
      "      begin #10 b = 8'd2; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

TEST(WaitForkSimulation, WaitForkAfterPlainJoinProceedsImmediately) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #5  a = 8'd1; end\n"
      "      begin #10 b = 8'd2; end\n"
      "    join\n"
      "    wait fork;\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

TEST(WaitForkSimulation, WaitForkInsideTaskWaitsForTaskSpawnedChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  task run();\n"
      "    fork\n"
      "      begin #5  a = 8'd1; end\n"
      "      begin #10 b = 8'd2; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "    c = a + b;\n"
      "  endtask\n"
      "  initial run();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

TEST(WaitForkSimulation, WaitForkOnlyWaitsForImmediateChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] marker;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        fork\n"
      "          begin\n"
      "            #10;\n"
      "            marker = 8'd99;\n"
      "          end\n"
      "        join_none\n"
      "      end\n"
      "    join_none\n"
      "    wait fork;\n"
      "    marker = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);

  LowerRunAndCheck(f, design, {{"marker", 99u}});
}

TEST(WaitForkSimulation, WaitForkWaitsForJoinAnyLeftoverChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, done;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd5;\n"
      "      begin #10 b = 8'd7; end\n"
      "    join_any\n"
      "    wait fork;\n"
      "    done = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 5u}, {"b", 7u}, {"done", 7u}});
}

TEST(WaitForkSimulation, WaitForkWaitsForChildrenSpawnedBySubroutine) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, done;\n"
      "  function void do_sequence();\n"
      "    fork\n"
      "      a = 8'd5;\n"
      "      begin #10 b = 8'd7; end\n"
      "    join_none\n"
      "  endfunction\n"
      "  initial begin\n"
      "    do_sequence();\n"
      "    wait fork;\n"
      "    done = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 5u}, {"b", 7u}, {"done", 7u}});
}

TEST(WaitForkSimulation, AKilledChildCountsAsTerminated) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t; process p, q;\n"
                 "  initial begin\n"
                 "    fork begin p = process::self(); #10; end join_none\n"
                 "    #1 p.kill();\n"
                 "    wait fork;\n"
                 "    $display(\"wait %0t\", $time);\n"
                 "    fork begin q = process::self(); #10; end join\n"
                 "    $display(\"join %0t\", $time);\n"
                 "  end\n"
                 "  initial #3 q.kill();\n"
                 "endmodule\n",
                 f),
      "wait 1\njoin 3\n");
}

}  // namespace
