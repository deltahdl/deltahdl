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

TEST(IpcSync, PlainNamedOperandsSucceedInOrderAndFailOutOfOrder) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  event e0, e1, e2;\n"
                 "  bit ok;\n"
                 "  task automatic run(int which);\n"
                 "    fork\n"
                 "      begin\n"
                 "        case (which)\n"
                 "          0: wait_order(e0, e1) ok = 1; else ok = 0;\n"
                 "          1: wait_order(e0, e2) ok = 1; else ok = 0;\n"
                 "          2: wait_order(e0, e2) ok = 1; else ok = 0;\n"
                 "          3: wait_order(e1, e2) ok = 1; else ok = 0;\n"
                 "          default: wait_order(e0, e1) ok = 1; else ok = 0;\n"
                 "        endcase\n"
                 "        $display(\"%0d ok=%0d at %0t\", which, ok, $time);\n"
                 "      end\n"
                 "      begin\n"
                 "        case (which)\n"
                 "          0: begin #1 -> e0; #1 -> e1; end\n"
                 "          1, 2: begin #1 -> e0; #1 -> e2; end\n"
                 "          3: begin #1 -> e1; #1 -> e2; end\n"
                 "          default: begin #1 -> e1; #1 -> e0; end\n"
                 "        endcase\n"
                 "      end\n"
                 "    join_any\n"
                 "    #5;\n"
                 "  endtask\n"
                 "  initial for (int k = 0; k < 5; k++) run(k);\n"
                 "endmodule\n",
                 f),
      "0 ok=1 at 2\n1 ok=1 at 9\n2 ok=1 at 16\n3 ok=1 at 23\n4 ok=0 at 29\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IpcSync, DISABLED_DottedOperandsSucceedInOrderAndFailOutOfOrder) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc;\n"
          "  event ie;\n"
          "endinterface\n"
          "module m;\n"
          "  ifc i();\n"
          "  event e0, e2;\n"
          "  bit ok;\n"
          "  task automatic run(int which);\n"
          "    fork\n"
          "      begin\n"
          "        case (which)\n"
          "          0: wait_order(e0, i.ie) ok = 1; else ok = 0;\n"
          "          1: wait_order(e0, $root.m.e2) ok = 1; else ok = 0;\n"
          "          2: wait_order(e0, m.e2) ok = 1; else ok = 0;\n"
          "          3: wait_order(i.ie, e2) ok = 1; else ok = 0;\n"
          "          default: wait_order(e0, i.ie) ok = 1; else ok = 0;\n"
          "        endcase\n"
          "        $display(\"%0d ok=%0d at %0t\", which, ok, $time);\n"
          "      end\n"
          "      begin\n"
          "        case (which)\n"
          "          0: begin #1 -> e0; #1 -> i.ie; end\n"
          "          1, 2: begin #1 -> e0; #1 -> e2; end\n"
          "          3: begin #1 -> i.ie; #1 -> e2; end\n"
          "          default: begin #1 -> i.ie; #1 -> e0; end\n"
          "        endcase\n"
          "      end\n"
          "    join_any\n"
          "    #5;\n"
          "  endtask\n"
          "  initial for (int k = 0; k < 5; k++) run(k);\n"
          "endmodule\n",
          f),
      "0 ok=1 at 2\n1 ok=1 at 9\n2 ok=1 at 16\n3 ok=1 at 23\n4 ok=0 at 29\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
