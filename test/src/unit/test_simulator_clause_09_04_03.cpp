#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSimulation, WaitConditionBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    #10 ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (ready) x = 8'd88;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(LevelSensitiveEventSimulation, WaitAlreadyTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait (1) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

bool EvaluateWaitCondition(uint64_t value) { return value != 0; }

TEST(LevelSensitiveEventSimulation, WaitConditionTrueUnblocks) {
  EXPECT_TRUE(EvaluateWaitCondition(1));
}

TEST(LevelSensitiveEventSimulation, WaitConditionFalseBlocks) {
  EXPECT_FALSE(EvaluateWaitCondition(0));
}

TEST(LevelSensitiveEventSimulation, WaitStatementNullBody) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait(1) ;\n"
      "    x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

TEST(LevelSensitiveEventSimulation, WaitXConditionBlocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic cond;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cond = 1'bx;\n"
      "    x = 8'd0;\n"
      "    wait (cond) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveEventSimulation, WaitZConditionBlocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic cond;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cond = 1'bz;\n"
      "    x = 8'd0;\n"
      "    wait (cond) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveEventSimulation, WaitConditionWithDelayInBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 0;\n"
      "    b = 8'd55;\n"
      "    #5 enable = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(LevelSensitiveEventSimulation, WaitMultipleSignalCondition) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "    #5 a = 1;\n"
      "    #5 b = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (a && b) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

TEST(LevelSensitiveEventSimulation, WaitZeroConditionNeverUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (0) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

}  // namespace
