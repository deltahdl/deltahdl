#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveSequenceSimulation, WaitBlocksUntilSequenceEndpoint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  logic [7:0] result;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; result = 0;\n"
      "    #1 a = 1; clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; clk = 1; #1 clk = 0;\n"
      "    #1 c = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "    result = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LevelSensitiveSequenceSimulation, WaitWithBodyStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] result;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; result = 0;\n"
      "    #1 a = 1; clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial\n"
      "    wait(ab.triggered) result = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(LevelSensitiveSequenceSimulation, TriggeredFalseBeforeMatch) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] early;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0;\n"
      "    early = ab.triggered ? 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "early");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveSequenceSimulation, TriggeredPersistsThroughTimeStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] which;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; which = 0;\n"
      "    #1 a = 1; clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "    if (s1.triggered) which = 8'd1;\n"
      "    else if (s2.triggered) which = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("which");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.ToUint64(), 0u);
}

TEST(LevelSensitiveSequenceSimulation, TriggeredResetsOnNewTimeStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] after_advance;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; after_advance = 8'hff;\n"
      "    #1 a = 1; clk = 1; #1 clk = 0;\n"
      "    #1 b = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(ab.triggered);\n"
      "    #1;\n"
      "    after_advance = ab.triggered ? 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("after_advance");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LevelSensitiveSequenceSimulation, WaitMultipleTriggeredOr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c, d;\n"
      "  logic [7:0] result;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; c = 0; d = 0; result = 0;\n"
      "    #1 c = 1; clk = 1; #1 clk = 0;\n"
      "    #1 d = 1; clk = 1; #1 clk = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "    result = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(LevelSensitiveSequenceSimulation, WaitSequenceTriggeredDoesNotFireBeforeMatch) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [7:0] result;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 0; result = 0;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    wait(ab.triggered);\n"
      "    result = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 0u);
}

}  // namespace
