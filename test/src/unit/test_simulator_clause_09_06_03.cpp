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

TEST(DisableForkExecution, ExecutionContinuesAfterDisableFork) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10; x = 8'd99; end\n"
      "    join_none\n"
      "    disable fork;\n"
      "    y = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}, {"y", 1u}});
}

}  // namespace
