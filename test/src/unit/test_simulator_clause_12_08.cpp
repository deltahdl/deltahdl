#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(JumpStatementSim, JumpBreakExitsLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(JumpStatementSim, JumpReturnVoidFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LoopStatementSim, ForeverContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, RepeatBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, WhileBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopStatementSim, ForBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, ForContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, DoWhileBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, DoWhileContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, NestedLoopInnerBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("outer_count");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(JumpStatementSim, JumpReturnWithValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int double_val(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = double_val(21);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(JumpStatementSim, JumpReturnEarlyFromFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(LoopStatementSim, ForeachContinueSkipsCurrentIteration) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(JumpStatementSim, JumpBreakExitsMultiDimForeach) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(JumpStatementSim, JumpContinueInMultiDimForeach) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] matrix [2][3];\n"
      "  logic [7:0] skipped;\n"
      "  initial begin\n"
      "    skipped = 8'd0;\n"
      "    foreach (matrix[i, j]) begin\n"
      "      continue;\n"
      "      skipped = skipped + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("skipped");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LoopStatementSim, NestedLoopInnerContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 9u);
}

}  // namespace
