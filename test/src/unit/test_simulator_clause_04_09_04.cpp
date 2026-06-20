#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

TEST(NonblockingAssignSchedulingSim, SchedulesUpdateInNbaRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, snap;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    dst <= 8'd7;\n"
      "    snap = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
}

TEST(NonblockingAssignSchedulingSim, ZeroDelaySchedulesInCurrentTimestep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    dst <= 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(NonblockingAssignSchedulingSim, NonzeroDelaySchedulesAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst, mid;\n"
      "  initial begin\n"
      "    dst = 8'd0;\n"
      "    mid = 8'd0;\n"
      "    dst <= #10 8'd99;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 mid = dst;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(NonblockingAssignSchedulingSim, RhsUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = 8'd0;\n"
      "    dst <= src;\n"
      "    src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
}

TEST(NonblockingAssignSchedulingSim, LhsTargetUsesValuesAtScheduleTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] <= 8'hCC;\n"
      "    idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0xCCu);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0u);
}
