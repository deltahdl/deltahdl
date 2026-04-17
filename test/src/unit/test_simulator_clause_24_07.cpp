#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProgramControlTasksSim, ExitFromProgramInitialRequestsStop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    initial $exit();\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
}

TEST(ProgramControlTasksSim, ExitSkipsSubsequentStatementsInProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial begin\n"
      "      $exit();\n"
      "      v = 8'd99;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitTerminatesPeerProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial $exit();\n"
      "    initial begin\n"
      "      #100 v = 8'd77;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitFromForkedDescendantTerminatesProgramInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p;\n"
      "    initial begin\n"
      "      fork\n"
      "        $exit();\n"
      "      join\n"
      "      v = 8'd55;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.StopRequested());
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(ProgramControlTasksSim, ExitFromModuleInitialIsIgnored) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    $exit();\n"
      "    v = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
  EXPECT_FALSE(f.ctx.StopRequested());
}

TEST(ProgramControlTasksSim, ExitFromModuleAlwaysIsIgnored) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    v = 8'd0;\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 v = 8'd7;\n"
      "  end\n"
      "  always @(posedge clk) $exit();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

TEST(ProgramControlTasksSim, ExitDoesNotTerminateOtherProgramBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'd0;\n"
      "  program p1;\n"
      "    initial $exit();\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial v = 8'd33;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

}  // namespace
