#include <cstdint>
#include <string>
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
  // §9.6.2: disabling a named block that is not currently executing has no
  // effect. Here done_early completes at time 0; the later disable finds no
  // active process for that scope, so it is a no-op and the disabling process
  // continues normally to the following statement.
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
  // §9.6.2 lists inout arguments (alongside output arguments) among the
  // activities whose results are unspecified once a task is disabled. Disabling
  // a task with a pending inout write must remain well-behaved (no crash).
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
  // §9.6.2 lists procedural continuous assignments from both `assign` and
  // `force` as activities whose results are unspecified when the task is
  // disabled. Exercise the `force` form to keep disable robust for it too.
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

// §9.6.2: "The disable statement shall terminate the activity of a task or a
// named block. Execution shall resume at the statement following the block or
// following the task-enabling statement." Runs `rules` as the body of a
// randsequence written inside the named block `blk`. `in_rs` is written by a
// code block of the randsequence, `after_rs` by the statement standing after
// the randsequence and still inside `blk`, and `after_blk` by the statement
// standing after `blk`. A `disable blk` the rules reach therefore terminates
// `blk`, leaving `after_rs` unwritten, and resumes at `after_blk`. The two
// cases below differ only in which of the code blocks §18.17.1 admits holds
// the disable, so they share the module, the lowering and the run.
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

// §9.6.2: "The disable statement can be used within blocks and tasks to
// disable the particular block or task containing the disable statement", and
// disabling a named block terminates it, execution resuming at the statement
// following the block. A production code block of a randsequence written
// inside `blk` is inside `blk`, so the disable it executes terminates `blk`
// rather than being absorbed by the randsequence: §18.17.6 gives a randsequence
// a meaning for break and for return and none for disable.
TEST(DisableStatementExecution,
     DisableInARandsequenceProductionCodeBlockTerminatesTheBlock) {
  SimFixture f;
  RunRandseqDisableTrial(f,
                         "        main : { in_rs = 8'd37; disable blk; };\n");
}

// §18.17.1 and Syntax 18-14 write a rule as
// `rs_production_list [ := rs_weight_specification [ rs_code_block ] ]`, so a
// code block may follow a weight as well as stand as a production. §9.6.2 makes
// no distinction between them: a disable executed in either terminates the
// named block containing the randsequence. This is a second statement list,
// run by a loop of its own, so the production-code-block case does not answer
// for it. §18.17.7 puts this block after the rule's production list, so `alt`
// writes `in_rs` before the weight code block disables `blk`.
TEST(DisableStatementExecution,
     DisableInARandsequenceWeightCodeBlockTerminatesTheBlock) {
  SimFixture f;
  RunRandseqDisableTrial(f,
                         "        main : alt := 5 { disable blk; };\n"
                         "        alt : { in_rs = 8'd37; };\n");
}

}  // namespace
