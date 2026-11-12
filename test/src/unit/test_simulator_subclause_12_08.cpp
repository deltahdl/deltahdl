#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_statement_in_every_procedure.h"
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

TEST(JumpStatementSim, BreakEndsForeverLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_four();\n"
                      "    static int n = 0;\n"
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

TEST(JumpStatementSim, BreakEndsForLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int sum_below_five();\n"
                      "    static int sum = 0;\n"
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

TEST(JumpStatementSim, BreakEndsWhileLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_six();\n"
                      "    static int i = 0;\n"
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

TEST(JumpStatementSim, BreakEndsDoWhileLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_three();\n"
                      "    static int i = 0;\n"
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

TEST(JumpStatementSim, BreakEndsForeachLoopInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[8];\n"
                      "  int r;\n"
                      "  function int count_to_index_three();\n"
                      "    static int cnt = 0;\n"
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

TEST(JumpStatementSim, ContinueRunsForStepInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int sum_evens();\n"
                      "    static int sum = 0;\n"
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

TEST(JumpStatementSim, BreakInsideNestedBlockInFunctionLoop) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_seven();\n"
                      "    static int n = 0;\n"
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

TEST(JumpStatementSim, BreakEndsLabeledForeverInFunction) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int count_to_five();\n"
                      "    static int n = 0;\n"
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

TEST(LoopStatementSim, ContinueJumpsToEndOfWhileBody) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    while (x < 8'd6) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 5u);
}

constexpr const char* kJumpLoops[] = {
    ("for (int i = 1; i <= 5; i++) begin if (i == 2) continue; if (i == 4) "
     "break; r += i; end\n"),
    ("begin int i; i = 0; repeat (5) begin i++; if (i == 2) continue; if (i "
     "== 4) break; r += i; end end\n"),
    ("begin int i; i = 0; while (i < 5) begin i++; if (i == 2) continue; if "
     "(i == 4) break; r += i; end end\n"),
    ("begin int i; i = 0; do begin i++; if (i == 2) continue; if (i == 4) "
     "break; r += i; end while (i < 5); end\n"),
    ("begin int i; i = 0; forever begin i++; if (i == 2) continue; if (i == "
     "4) break; r += i; end end\n"),
    ("begin int a [1:5]; foreach (a[i]) begin if (i == 2) continue; if (i == "
     "4) break; r += i; end end\n")};

TEST(JumpStatementSim, BreakAndContinueWorkInEveryLoopOfEveryProcedure) {
  for (const char* loop : kJumpLoops) {
    SimFixture f;
    EXPECT_EQ(RunCapture(StatementInEveryProcedure(loop), f),
              "4 4 4 4 4\nG 4\nI 4\nP 4\n")
        << loop;
    EXPECT_EQ(f.diag.WarningCount(), 0u) << loop;
  }
}

TEST(JumpStatementSim, ReturnLeavesEveryKindOfSubroutine) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  function automatic int pf(int x);\n"
                       "    if (x > 0) return x * 2;\n"
                       "    return -1;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "import pk::*;\n"
                       "function automatic int cf(int x);\n"
                       "  if (x > 0) return x + 100;\n"
                       "  return -2;\n"
                       "endfunction\n"
                       "class C;\n"
                       "  int log;\n"
                       "  function void vm(int x);\n"
                       "    log = 1;\n"
                       "    if (x > 0) return;\n"
                       "    log = 2;\n"
                       "  endfunction\n"
                       "  task tm(int x);\n"
                       "    #1 if (x > 0) return;\n"
                       "    log = 3;\n"
                       "  endtask\n"
                       "endclass\n"
                       "interface I;\n"
                       "  function int f(int x);\n"
                       "    if (x > 0) return 7;\n"
                       "    return 8;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "program p;\n"
                       "  task automatic t(output int r);\n"
                       "    r = 1;\n"
                       "    return;\n"
                       "    r = 2;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    int r;\n"
                       "    #5 t(r);\n"
                       "    $display(\"P %0d\", r);\n"
                       "  end\n"
                       "endprogram\n"
                       "module t;\n"
                       "  I u();\n"
                       "  p pp();\n"
                       "  initial begin\n"
                       "    C c;\n"
                       "    c = new;\n"
                       "    $display(\"%0d %0d %0d %0d\", pf(3), pf(0), cf(1), "
                       "cf(0));\n"
                       "    $display(\"%0d %0d\", u.f(1), u.f(0));\n"
                       "    c.vm(1);\n"
                       "    $write(\"%0d \", c.log);\n"
                       "    c.vm(0);\n"
                       "    $write(\"%0d \", c.log);\n"
                       "    c.tm(1);\n"
                       "    $write(\"%0d \", c.log);\n"
                       "    c.tm(0);\n"
                       "    $display(\"%0d %0t\", c.log, $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "6 -1 101 -2\n7 8\n1 2 2 3 2\nP 1\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
