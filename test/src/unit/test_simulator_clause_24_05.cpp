#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockingTasksCycleEventMode,
     ModuleTaskCalledFromModuleBlockingRunsInActive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  task write_v(input logic [7:0] val);\n"
      "    v = val;\n"
      "  endtask\n"
      "  initial v <= 8'd10;\n"
      "  initial write_v(8'd99);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(BlockingTasksCycleEventMode,
     ModuleTaskCalledFromProgramBlockingRunsInReactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] v;\n"
      "  task write_v(input logic [7:0] val);\n"
      "    v = val;\n"
      "  endtask\n"
      "  initial v <= 8'd10;\n"
      "  program p;\n"
      "    initial write_v(8'd99);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(BlockingTasksCycleEventMode,
     ModuleTaskNonBlockingCalledFromProgramCommitsInReNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  task nba_copy;\n"
      "    b <= a;\n"
      "  endtask\n"
      "  initial a <= 8'd42;\n"
      "  program p;\n"
      "    initial nba_copy();\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 42u);
}

TEST(BlockingTasksCycleEventMode,
     ModuleFunctionCalledFromProgramReturnsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int r;\n"
      "  function automatic int add_one(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  program p;\n"
      "    initial r = add_one(41);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 42u);
}

}  // namespace
