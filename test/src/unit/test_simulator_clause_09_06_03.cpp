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

// --- R1: disable fork terminates all descendant subprocesses ---

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

// --- R1: terminates descendants, not just immediate children ---

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

// --- R2: disable fork after join_any kills remaining children ---

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

// --- R3: disable fork considers dynamic parent-child relationships ---
// --- R4: disable fork ends only processes spawned by the calling thread ---

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

// --- Edge case: disable fork with no children is a no-op ---

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

// --- Edge case: execution continues after disable fork ---

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
