#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(JumpStatementSim, JumpBreakExitsLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(JumpStatementSim, JumpReturnVoidFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x();\n"
      "    x = 8'd10;\n"
      "    return;\n"
      "    x = 8'd20;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    set_x();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.8 runtime return rule exercised through a §13.3 task built from real
// source: an early return exits the task, so the statement after it never runs.
TEST(JumpStatementSim, JumpReturnExitsTask) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_early();\n"
      "    x = 8'd7;\n"
      "    return;\n"
      "    x = 8'd9;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_early();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// continue (12.8) is taken on every odd iteration of a forever-loop, and
// the loop keeps running until the break. The 12.7.6 file makes the
// matching claim about the forever-loop construct.
TEST(LoopStatementSim, ContinueSkipsOddForeverIterations) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd10) break;\n"
      "      if (x[0]) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, RepeatBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (100) begin\n"
      "      if (x == 8'd3) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatContinue) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    repeat (5) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

// break jumps out of the loop (12.8); the while control expression never
// goes false, so break is the only way out. The 12.7.4 file makes the
// matching claim about the while-loop construct.
TEST(LoopStatementSim, BreakJumpsOutOfWhileLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    while (1) begin\n"
      "      if (x == 8'd7) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopStatementSim, ForBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    for (int i = 0; i < 100; i = i + 1) begin\n"
      "      if (i == 3) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// continue (12.8) is taken on two selected iterations of one for-loop, and
// the loop control still runs the remaining iterations. The 12.7.1 file
// makes the matching claim about the for-loop construct.
TEST(LoopStatementSim, ContinueSkipsSelectedForIterations) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] count;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    for (int i = 0; i < 6; i = i + 1) begin\n"
      "      if (i == 2 || i == 4) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// break jumps out of the do...while loop (12.8) even though its control
// expression is constantly true. The 12.7.5 file makes the matching claim
// about the do...while construct's end-of-loop test.
TEST(LoopStatementSim, BreakJumpsOutOfDoWhileLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) break;\n"
      "    end while (1);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// continue jumps to the end of the loop (12.8), skipping the rest of the
// do...while body on the selected iteration. The 12.7.5 file makes the
// matching claim about the do...while construct's end-of-loop test.
TEST(LoopStatementSim, ContinueSkipsRemainderOfDoWhileBody) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    do begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end while (x < 8'd5);\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, NestedLoopInnerBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] outer_count;\n"
      "  initial begin\n"
      "    outer_count = 8'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      for (int j = 0; j < 100; j = j + 1) begin\n"
      "        if (j == 2) break;\n"
      "      end\n"
      "      outer_count = outer_count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "outer_count");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(JumpStatementSim, JumpReturnWithValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int double_val(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = double_val(21);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(JumpStatementSim, JumpReturnEarlyFromFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int clamp(int v);\n"
      "    if (v > 10) return 10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = clamp(50);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LoopStatementSim, ContinueRunsForLoopStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, step_count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    step_count = 8'd0;\n"
      "    for (int i = 0; i < 4; step_count = step_count + 8'd1,"
      " i = i + 1) begin\n"
      "      if (i == 1) continue;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* step = f.ctx.FindVariable("step_count");
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(step, nullptr);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(step->value.ToUint64(), 4u);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForeachBreakExitsLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [5];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd2) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(LoopStatementSim, ForeachContinueSkipsCurrentIteration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    arr[0] = 8'd1;\n"
      "    arr[1] = 8'd2;\n"
      "    arr[2] = 8'd3;\n"
      "    arr[3] = 8'd4;\n"
      "    sum = 8'd0;\n"
      "    foreach (arr[i]) begin\n"
      "      if (i[7:0] == 8'd2) continue;\n"
      "      sum = sum + arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(JumpStatementSim, JumpBreakExitsMultiDimForeach) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] matrix [2][3];\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    cnt = 8'd0;\n"
      "    foreach (matrix[i, j]) begin\n"
      "      cnt = cnt + 8'd1;\n"
      "      if (cnt == 8'd1) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// continue (12.8) is taken on every odd iteration of one while-loop. The
// 12.8.2 file covers a single continue and the 12.7.4 file makes the
// matching claim about the while-loop construct.
TEST(LoopStatementSim, ContinueSkipsOddWhileIterations) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    while (x < 8'd10) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x[0]) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // continue jumps back to the while condition, skipping the count bump on odd
  // values; the loop still runs to completion, tallying the five even values.
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

TEST(JumpStatementSim, ContinueAdvancesMultiDimForeach) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] matrix [2][3];\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    matrix[0][0] = 8'd1;\n"
      "    matrix[0][1] = 8'd2;\n"
      "    matrix[0][2] = 8'd3;\n"
      "    matrix[1][0] = 8'd4;\n"
      "    matrix[1][1] = 8'd5;\n"
      "    matrix[1][2] = 8'd6;\n"
      "    sum = 8'd0;\n"
      "    foreach (matrix[i, j]) begin\n"
      "      if (matrix[i][j] == 8'd3) continue;\n"
      "      sum = sum + matrix[i][j];\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // In a multidimensional foreach, continue ends only the current set of loop
  // variable values and proceeds to the next combination, so every element but
  // the skipped 3 is summed: 1+2+4+5+6 == 18.
  auto* sum = f.ctx.FindVariable("sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 18u);
}

TEST(LoopStatementSim, NestedLoopInnerContinue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      for (int j = 0; j < 4; j = j + 1) begin\n"
      "        if (j == 1) continue;\n"
      "        total = total + 8'd1;\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// §12.8: a break jumps out of the loop, and §13.4 lets a function body hold
// the loop. The loop is bounded by a return at 99 so that a break the
// interpreter passed over gives 99 rather than a run that never ends; with
// the break acted on the count is 4.
TEST(JumpStatementSim, BreakEndsForeverLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_four();\n"
                      "    int n = 0;\n"
                      "    forever begin\n"
                      "      n = n + 1;\n"
                      "      if (n == 4) break;\n"
                      "      if (n == 99) return n;\n"
                      "    end\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "  initial r = count_to_four();\n"
                      "endmodule\n",
                      "r"),
            4u);
}

// A break in a for loop of a function body leaves the loop before the step:
// the values 0 to 4 are summed, 10, where a loop the break did not end sums
// 0 to 9, 45.
TEST(JumpStatementSim, BreakEndsForLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int sum_below_five();\n"
                      "    int sum = 0;\n"
                      "    for (int i = 0; i < 10; i = i + 1) begin\n"
                      "      if (i == 5) break;\n"
                      "      sum = sum + i;\n"
                      "    end\n"
                      "    return sum;\n"
                      "  endfunction\n"
                      "  initial r = sum_below_five();\n"
                      "endmodule\n",
                      "r"),
            10u);
}

// A break in a while loop of a function body: the counter stops at 6 where
// the condition alone would run it to 10.
TEST(JumpStatementSim, BreakEndsWhileLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_six();\n"
                      "    int i = 0;\n"
                      "    while (i < 10) begin\n"
                      "      i = i + 1;\n"
                      "      if (i == 6) break;\n"
                      "    end\n"
                      "    return i;\n"
                      "  endfunction\n"
                      "  initial r = count_to_six();\n"
                      "endmodule\n",
                      "r"),
            6u);
}

// A break in a do-while loop of a function body leaves before the condition
// is read again: the counter stops at 3 where the condition alone runs it to
// 10.
TEST(JumpStatementSim, BreakEndsDoWhileLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_three();\n"
                      "    int i = 0;\n"
                      "    do begin\n"
                      "      i = i + 1;\n"
                      "      if (i == 3) break;\n"
                      "    end while (i < 10);\n"
                      "    return i;\n"
                      "  endfunction\n"
                      "  initial r = count_to_three();\n"
                      "endmodule\n",
                      "r"),
            3u);
}

// A break in a foreach loop of a function body jumps out of the whole loop:
// three elements are counted before the index reaches 3, where a loop the
// break did not end counts all eight.
TEST(JumpStatementSim, BreakEndsForeachLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[8];\n"
                      "  int r;\n"
                      "  function int count_to_index_three();\n"
                      "    int cnt = 0;\n"
                      "    foreach (arr[k]) begin\n"
                      "      if (k == 3) break;\n"
                      "      cnt = cnt + 1;\n"
                      "    end\n"
                      "    return cnt;\n"
                      "  endfunction\n"
                      "  initial r = count_to_index_three();\n"
                      "endmodule\n",
                      "r"),
            3u);
}

// §12.8: a continue jumps to the end of the loop body and the loop control
// then runs, so the for loop's step is what carries it past the odd values:
// the even values below 10 sum to 20, where a continue that skipped nothing
// sums every value to 45, and one that skipped the step never reaches 10.
TEST(JumpStatementSim, ContinueRunsForStepInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int sum_evens();\n"
                      "    int sum = 0;\n"
                      "    for (int i = 0; i < 10; i = i + 1) begin\n"
                      "      if (i % 2 == 1) continue;\n"
                      "      sum = sum + i;\n"
                      "    end\n"
                      "    return sum;\n"
                      "  endfunction\n"
                      "  initial r = sum_evens();\n"
                      "endmodule\n",
                      "r"),
            20u);
}

// The shape of uvm_report_server::reset_severity_counts: a class method
// walks an enumeration from first() to last() with next() (§6.19.5) in a
// forever loop that breaks at the last member. Four members are visited;
// the guard at 99 turns a break the method did not act on into 99 rather
// than a run that never ends.
TEST(JumpStatementSim, BreakEndsEnumForeverInClassMethod) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef enum { INFO, WARNING, ERROR, FATAL } sev_t;\n"
                      "  class server;\n"
                      "    int visited;\n"
                      "    function void reset_counts();\n"
                      "      sev_t s;\n"
                      "      visited = 0;\n"
                      "      s = s.first();\n"
                      "      forever begin\n"
                      "        visited = visited + 1;\n"
                      "        if (s == s.last()) break;\n"
                      "        if (visited == 99) return;\n"
                      "        s = s.next();\n"
                      "      end\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    server srv;\n"
                      "    srv = new;\n"
                      "    srv.reset_counts();\n"
                      "    r = srv.visited;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            4u);
}

// The break stands in a begin-end block inside an if inside the loop, and
// each of the block and the if hands it up to the loop: the count stops at 7,
// where a break the block or the if consumed gives 99.
TEST(JumpStatementSim, BreakInsideNestedBlockInFunctionLoop) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_seven();\n"
                      "    int n = 0;\n"
                      "    forever begin\n"
                      "      n = n + 1;\n"
                      "      if (n > 2) begin\n"
                      "        if (n == 7) begin\n"
                      "          break;\n"
                      "        end\n"
                      "      end\n"
                      "      if (n == 99) return n;\n"
                      "    end\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "  initial r = count_to_seven();\n"
                      "endmodule\n",
                      "r"),
            7u);
}

// A labeled loop in a function body (§9.3.5) is left by a break as an
// unlabeled one is, and the statement after it runs: the count stops at 5
// and the return past the loop adds 100, so 105 where the loop ended at the
// 99 guard would give 199.
TEST(JumpStatementSim, BreakEndsLabeledForeverInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_five();\n"
                      "    int n = 0;\n"
                      "    scan : forever begin\n"
                      "      n = n + 1;\n"
                      "      if (n == 5) break;\n"
                      "      if (n == 99) break;\n"
                      "    end\n"
                      "    return n + 100;\n"
                      "  endfunction\n"
                      "  initial r = count_to_five();\n"
                      "endmodule\n",
                      "r"),
            105u);
}

}  // namespace
