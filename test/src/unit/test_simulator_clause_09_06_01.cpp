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

TEST(WaitForkSimulation, WaitForkAfterPlainJoinProceedsImmediately) {
  // §9.6.1 blocks until every immediate child subprocess has terminated. When
  // the children were spawned with a plain fork...join, the join site has
  // already waited for all of them, so at the following wait fork there are no
  // outstanding immediate children and execution must proceed without blocking.
  // This exercises the third fork join kind of the §9.3.2 dependency: the child
  // tally the join drained leaves nothing for wait fork to wait on, yet wait
  // fork must not hang. The read still observes both writes (c == 3) because
  // the join already ran both children through time 10.
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
  // §9.6.1's rule applies wherever wait fork appears, including inside a task
  // body -- the syntactic position of the LRM's do_test example. The task forks
  // two immediate children with join_none and then executes wait fork; because
  // the task body runs in the caller's process, those children are immediate
  // child subprocesses of that process and wait fork must block until the last
  // one terminates at time 10. If wait fork failed to block at the task-body
  // position the sum would be read early and c would not reach 3.
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

TEST(WaitForkSimulation, WaitForkWaitsForChildrenSpawnedBySubroutine) {
  // §9.6.1 defines an immediate child subprocess as one created by the current
  // process. The LRM example spawns some immediate children not from an inline
  // fork but from a fork...join_none inside a subroutine (do_sequence) that the
  // current process calls; those still belong to the caller's process, so a
  // following wait fork must block until they terminate. Here do_sequence
  // returns immediately after spawning two background children -- one writing
  // at time 0, one at time 10. If wait fork ignored subroutine-spawned children
  // it would resume at time 0 and sample b before the delayed write, leaving
  // done at 0; only waiting through time 10 yields done == 7.
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

}  // namespace
