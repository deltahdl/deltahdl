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

TEST(WaitForkSimulation, WaitForkWaitsForLastOfStaggeredChildren) {
  // Two immediate children spawned with join_none terminate at different
  // simulation times. §9.6.1 requires wait fork to remain blocked until the
  // later-finishing child terminates, not merely the first, so the read after
  // wait fork observes both writes. If wait fork resumed at time 5 the sum
  // would be 1; only waiting through time 10 yields 3.
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
  // join_any unblocks as soon as the immediate child completes, but the
  // delayed sibling is still an immediate child subprocess. §9.6.1 requires a
  // following wait fork to block until that sibling terminates too, so the
  // assignment after wait fork observes the delayed write.
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

}
