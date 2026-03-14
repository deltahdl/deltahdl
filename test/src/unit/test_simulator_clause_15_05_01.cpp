#include <gtest/gtest.h>

#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace {

// §15.5.1: Event variable creation in simulator.
TEST(IpcSync, EventVariableCreation) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

// §15.5.1: Blocking trigger unblocks a process waiting via @(ev).
TEST(IpcSync, BlockingTriggerUnblocksWaiter) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 42;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 ->ev;\n"
      "    #1 $finish;\n"
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

// §15.5.1: Bare @ev wait syntax works with blocking trigger.
TEST(IpcSync, BareWaitSyntaxWithTrigger) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @ev;\n"
      "    result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #3 ->ev;\n"
      "    #1 $finish;\n"
      "  end\n"
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

// §15.5.1: Trigger sets value after wait unblocks.
TEST(IpcSync, TriggerSetsValueAfterWait) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "  end\n"
      "  initial begin\n"
      "    @(ev) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §15.5.1: Nonblocking trigger (->> ev) unblocks a waiting process.
TEST(IpcSync, NonblockingTriggerUnblocksWaiter) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 77;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 ->> ev;\n"
      "    #2 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §15.5.1: Nonblocking trigger with delay unblocks waiter at delayed time.
TEST(IpcSync, NonblockingTriggerWithDelay) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 88;\n"
      "  end\n"
      "  initial begin\n"
      "    ->> #10 ev;\n"
      "    #20 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// §15.5.1: Blocking trigger unblocks multiple waiting processes.
TEST(IpcSync, TriggerUnblocksMultipleWaiters) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    a = 8'd11;\n"
      "  end\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    b = 8'd22;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 11u);
  EXPECT_EQ(vb->value.ToUint64(), 22u);
}


}  // namespace
