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

TEST(WaitForkSimulation, WaitForkBlocksUntilAllChildrenComplete) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "    join_none\n"
      "    wait fork;\n"
      "    c = a + b;\n"
      "  end\n"
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
  // Correct behavior: wait fork returns at time 0 (immediate child finished),
  // marker=1 at time 0, then grandchild sets marker=99 at time 10.
  // If wait fork incorrectly waited for the grandchild, marker=99 would be set
  // first at time 10, then marker=1 after wait fork returns, yielding 1.
  LowerRunAndCheck(f, design, {{"marker", 99u}});
}

}  // namespace
