#include <gtest/gtest.h>

#include <string_view>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace {

TEST(EventTriggerSimulator, BlockingTriggerUnblocksWaiter) {
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

TEST(EventTriggerSimulator, NonblockingTriggerUnblocksWaiter) {
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

TEST(EventTriggerSimulator, NonblockingTriggerWithDelay) {
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

// The ->> operator defers the trigger to the nonblocking assignment region of
// the current time step. A process that registers its wait in the active region
// *after* the ->> statement (same time step) is therefore still unblocked,
// since the deferred trigger fires only once the active region has drained. An
// active-region (immediate) trigger would be lost here, leaving result == 0.
TEST(EventTriggerSimulator, NonblockingTriggerDefersToNbaRegion) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    ->> ev;\n"
      "    @(ev);\n"
      "    result = 99;\n"
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

TEST(EventTriggerSimulator, TriggerUnblocksMultipleWaiters) {
  LowerFixture f;
  auto [a, b] = RunModuleTwoVars(f,
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
                                 "a", "b");
  EXPECT_EQ(a, 11u);
  EXPECT_EQ(b, 22u);
}

// ->> with an event control creates its update event when the event control
// occurs (here, a posedge), not when the statement executes. The waiter is
// unblocked once the posedge arrives.
TEST(EventTriggerSimulator, NonblockingTriggerWaitsForEventControl) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> @(posedge clk) ev;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
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

// The update event is gated on the event control: if the event control never
// occurs, the named event is never triggered and a waiter stays blocked. This
// distinguishes the deferred behavior from an immediate trigger, which would
// have fired the already-registered waiter and left result == 55.
TEST(EventTriggerSimulator, NonblockingTriggerGatedOnEventControl) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> @(posedge clk) ev;\n"
      "    #10 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// The repeat-event form waits for the event control the given number of times
// before creating the update event. After a single posedge (sampled into mid)
// the event has not yet fired; only the second posedge triggers it.
TEST(EventTriggerSimulator, NonblockingTriggerRepeatEventControl) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  logic [31:0] result, mid;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    clk = 0;\n"
      "    ->> repeat(2) @(posedge clk) ev;\n"
      "    #5 clk = 1;\n"
      "    #2 clk = 0;\n"
      "    #2 mid = result;\n"
      "    #2 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* mid = f.ctx.FindVariable("mid");
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(mid, nullptr);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(mid->value.ToUint64(), 0u);
  EXPECT_EQ(result->value.ToUint64(), 55u);
}

}  // namespace
