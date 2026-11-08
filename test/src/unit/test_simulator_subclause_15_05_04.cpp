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

TEST(IpcSync, WaitOrderOnlyFirstEventUsesPersistentTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd5;\n"
      "    -> a;\n"
      "    -> b;\n"
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

TEST(WaitOrderSim, StatementsAfterTheWaitRunAsTheWaiter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event a, b;\n"
      "  int y;\n"
      "  initial begin\n"
      "    wait_order (a);\n"
      "    unique if (1) y = 1; else if (1) y = 2;\n"
      "    @(b);\n"
      "  end\n"
      "  initial begin\n"
      "    #0 -> a;\n"
      "    #0 -> b;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
