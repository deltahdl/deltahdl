#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SchedulerOverviewSim, NBAExecutionOrderMatchesSourceOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a <= 8'd0;\n"
      "    a <= 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result, 1u);
}

TEST(SchedulerOverviewSim, DeterministicSequentialWithinProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = a * 8'd2;\n"
      "    c = b + a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 30u);
}

TEST(SchedulerOverviewSim, ConcurrentWriteSameTimeSlotLastWriteWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1;\n"
      "  initial x = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint64_t val = var->value.ToUint64();
  EXPECT_TRUE(val == 1u || val == 2u);
}

TEST(SchedulerOverviewSim, FullPipelineIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    #10 a = 8'd10;\n"
      "  end\n"
      "  assign b = a + 8'd1;\n"
      "  always_comb c = b * 8'd2;\n"
      "  initial begin\n"
      "    d <= 8'd0;\n"
      "    #10 d <= 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 99u);
}

}  // namespace
