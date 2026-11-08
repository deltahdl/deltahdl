#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

using namespace delta;

namespace {

TEST(StmtExec, DisableForkReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDisableFork;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(DisableForkExecution, DisableForkTerminatesJoinNoneChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        #10;\n"
      "        x = 8'd42;\n"
      "      end\n"
      "    join_none\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableForkExecution, DisableForkTerminatesMultipleChildren) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10; a = 8'd1; end\n"
      "      begin #20; b = 8'd2; end\n"
      "    join_none\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0u}, {"b", 0u}});
}

TEST(DisableForkExecution, DisableForkTerminatesDescendantSubprocesses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task nested_fork;\n"
      "    fork\n"
      "      begin\n"
      "        #10;\n"
      "        x = 8'd42;\n"
      "      end\n"
      "    join_none\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork\n"
      "      nested_fork;\n"
      "    join_none\n"
      "    #1;\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(DisableForkExecution, DisableForkAfterJoinAnyKillsRemaining) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      begin #10; b = 8'd2; end\n"
      "    join_any\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 0u}});
}

TEST(DisableForkExecution, DisableForkOnlyAffectsCallingThread) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10; a = 8'd1; end\n"
      "    join_none\n"
      "    disable fork;\n"
      "  end\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10; b = 8'd2; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0u}, {"b", 2u}});
}

TEST(DisableForkExecution, DisableForkWithNoChildrenIsNoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    disable fork;\n"
      "    x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 1u}});
}

TEST(DisableForkExecution, WaitForkAfterDisableForkDoesNotBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10; x = 8'd99; end\n"
      "    join_none\n"
      "    disable fork;\n"
      "    wait fork;\n"
      "    y = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}, {"y", 1u}});
}

TEST(DisableForkExecution, DisableForkInsideTaskKillsRemainingWaiters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] hits, result;\n"
      "  task automatic get_first;\n"
      "    fork\n"
      "      begin #10; hits = hits + 8'd1; result = 8'd1; end\n"
      "      begin #20; hits = hits + 8'd1; end\n"
      "      begin #30; hits = hits + 8'd1; end\n"
      "    join_any\n"
      "    disable fork;\n"
      "  endtask\n"
      "  initial begin\n"
      "    hits = 8'd0;\n"
      "    get_first;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"hits", 1u}, {"result", 1u}});
}

TEST(DisableForkExecution, DisableForkSparesSameBlockInOtherThread) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  task automatic work(input int id);\n"
      "    #10;\n"
      "    if (id == 1) a = 8'd1;\n"
      "    else b = 8'd2;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fork work(1); join_none\n"
      "    disable fork;\n"
      "  end\n"
      "  initial begin\n"
      "    fork work(2); join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0u}, {"b", 2u}});
}

TEST(DisableForkExecution, ALaterWaitForkWaitsForItsOwnChildren) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t; int y;\n"
                       "  initial begin\n"
                       "    fork #5 y = 1; join_none\n"
                       "    disable fork;\n"
                       "    #1;\n"
                       "    fork #3 y = 2; join_none\n"
                       "    wait fork;\n"
                       "    $display(\"%0t y=%0d\", $time, y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 y=2\n");
}

}  // namespace
