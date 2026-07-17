#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

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

// Terminating every descendant must also retire the calling process's
// outstanding-children bookkeeping: once disable fork has killed the spawned
// subprocesses there is nothing left for a subsequent wait fork to block on, so
// it returns immediately and the following statement runs. Were the tally left
// standing, wait fork would suspend forever (the killed child can never resume
// to decrement it) and y would never be written.
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

// Mirrors the clause's own example: the disable fork sits inside a subroutine,
// after a join_any that unblocks on the first branch to finish. Once the #10
// branch completes (hits==1, result==1), disable fork -- from the task's own
// process -- terminates the two still-pending branches, so neither the #20 nor
// the #30 branch ever runs and hits stays at 1. This exercises the construct in
// a distinct syntactic position (within a called task rather than directly in
// an initial block) and confirms the calling process it operates on is the
// task's.
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

// Isolates the dynamic-parent-child 'shall': disable fork ends only what the
// calling thread spawned, NOT every process executing a given block. Both
// initial blocks fork a call to the SAME task work -- one static block executed
// by two distinct dynamic threads. The first thread's disable fork kills only
// its own work(1) instance (a stays 0), while the second thread's work(2)
// instance -- the same static block, spawned by a different thread -- is
// untouched and runs to completion (b becomes 2). A static-block disable would
// have ended both; disable fork spares the sibling thread's copy.
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

}  // namespace
