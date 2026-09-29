#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

namespace {

TEST(IpcSync, WaitOrderInOrderExecutesThenBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitOrderOutOfOrderExecutesElseBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 -> a;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, WaitOrderThreeEventsInOrder) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
      "    #1 -> c;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, WaitOrderThreeEventsOutOfOrder) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> c;\n"
      "    #1 -> b;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, WaitOrderNullActionSuccess) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [7:0] after;\n"
      "  initial begin\n"
      "    wait_order(a, b);\n"
      "    after = 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "after");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, WaitOrderFirstEventAlreadyTriggered) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> a;\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitOrderEmptyEventsCompletes) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait_order(a);\n"
      "    x = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §15.5.4: preceding events are not limited to occur only once. Once an event
// has occurred in the prescribed order, it can be triggered again without
// causing the construct to fail.
TEST(IpcSync, WaitOrderPrecedingEventMayRetrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) result = 1;\n"
      "    else result = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> a;\n"  // a re-triggers after already passing in order
      "    #1 -> b;\n"
      "    #1 -> c;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.4: only the first event in the list can wait for the persistent
// triggered state. A non-first event that is already triggered in the current
// time step must still be triggered afresh, so this sequence never completes
// and neither the action nor the fail statement runs.
TEST(IpcSync, WaitOrderOnlyFirstEventUsesPersistentTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd5;\n"
      "    -> a;\n"  // first event: persistent triggered state satisfies it
      "    -> b;\n"  // second event: persistent state must NOT satisfy it
      "    wait_order(a, b) result = 8'd1;\n"
      "    else result = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §15.5.4: when the else (fail) clause is omitted, a failed sequence generates
// a default run-time error by calling $error (see §20.10).
TEST(IpcSync, WaitOrderDefaultFailureCallsError) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    wait_order(a, b);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 -> a;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
}

TEST(IpcSync, WaitOrderElseOnlyBranch) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b)\n"
      "    else result = 77;\n"
      "    #2 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 -> a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §15.5.4 with §6.17: wait_order takes a class's event properties, `s.a` and
// `s.b` through a handle, as it takes declared events: triggered in order at
// 1 and 2 it succeeds at 2, and triggered out of order it takes the else
// branch, read as 1, 2 and 0 in 120. Found by name alone, the properties were
// watched by nothing and neither wait_order ever completed.
TEST(WaitOrderSim, ClassEventPropertiesAreWaitedOnInOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class S; event a, b; endclass\n"
      "  S s;\n"
      "  int ok, at, bad, r;\n"
      "  initial begin\n"
      "    s = new;\n"
      "    fork\n"
      "      begin wait_order(s.a, s.b) ok = 1; else ok = 0; at = $time; end\n"
      "      begin #1 -> s.a; #1 -> s.b; end\n"
      "    join\n"
      "    bad = 1;\n"
      "    fork\n"
      "      wait_order(s.a, s.b) bad = 1; else bad = 0;\n"
      "      begin #1 -> s.b; #1 -> s.a; end\n"
      "    join\n"
      "    r = ok * 100 + at * 10 + bad;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 120u);
}

}  // namespace
