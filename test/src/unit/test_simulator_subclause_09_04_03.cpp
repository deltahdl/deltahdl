#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSimulation, WaitConditionBlocks) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(LevelSensitiveEventSimulation, WaitAlreadyTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait (1) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
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

TEST(LevelSensitiveEventSimulation, WaitConditionWithDelayInBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "a");
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

TEST(LevelSensitiveEventSimulation, AFalseConditionReadingNothingBlocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (0);\n"
      "    x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveEventSimulation, WaitVariableAlreadyTrueProceeds) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic flag;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    flag = 1;\n"
      "    x = 8'd0;\n"
      "    wait (flag) x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 200u);
}

TEST(LevelSensitiveEventSimulation, WaitVectorNonzeroConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] cnt;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cnt = 4'd0;\n"
      "    x = 8'd0;\n"
      "    #5 cnt = 4'd6;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (cnt) x = 8'd123;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 123u);
}

TEST(LevelSensitiveEventSimulation, WaitNullBodyBlocksFollowingStatement) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] tag, x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    tag = 8'd10;\n"
      "    #5  tag = 8'd77;\n"
      "    #5  ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (ready) ;\n"
      "    x = tag;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

TEST(LevelSensitiveEventSimulation, WaitBlocksThenDelayedBodyExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 1;\n"
      "    b = 8'd10;\n"
      "    #5  b = 8'd55;\n"
      "    #5  enable = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 55u);
}

TEST(LevelSensitiveEventSimulation, WaitBlockBodyExecutesAfterUnblock) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic go;\n"
      "  logic [7:0] src, p, q;\n"
      "  initial begin\n"
      "    go = 0;\n"
      "    src = 8'd1;\n"
      "    #5  src = 8'd9;\n"
      "    #5  go = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    p = 8'd0;\n"
      "    q = 8'd0;\n"
      "    wait (go) begin\n"
      "      p = src;\n"
      "      q = p;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(val, 9u);
}

TEST(LevelSensitiveEventSimulation, WaitTwoStateIntConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  int count;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    x = 8'd0;\n"
      "    #5 count = 3;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (count) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(LevelSensitiveEventSimulation, WaitOnABitSelectResumesWhenThatBitChanges) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    x = 8'd0;\n"
      "    #10 v = 4'b0010;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (v[1]) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(LevelSensitiveEventSimulation, WaitResumesOnVoidFunctionWrite) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic gate;\n"
      "  logic [7:0] done;\n"
      "  function void open_gate;\n"
      "    gate = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    gate = 1'b0;\n"
      "    #5;\n"
      "    open_gate();\n"
      "  end\n"
      "  initial begin\n"
      "    done = 8'd3;\n"
      "    wait (gate) done = 8'd91;\n"
      "  end\n"
      "endmodule\n",
      f, "done");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 91u);
}

TEST(LevelSensitiveEventSimulation, WaitResumesOnAnIncrementOperatorWrite) {
  auto val = RunAndGet(
      "module t;\n"
      "  int i;\n"
      "  logic [7:0] tag, seen;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    tag = 8'd12;\n"
      "  end\n"
      "  initial begin\n"
      "    #5  tag = 8'd64;\n"
      "    #5  i++;\n"
      "    #5  i++;\n"
      "    #5  i++;\n"
      "  end\n"
      "  initial begin\n"
      "    seen = 8'd3;\n"
      "    wait (i == 3) seen = tag;\n"
      "  end\n"
      "endmodule\n",
      "seen");
  EXPECT_EQ(val, 64u);
}

TEST(LevelSensitiveEventSimulation, WaitOnAnOwnPropertyInsideAClassTask) {
  auto val = RunAndGet(
      "class C;\n"
      "  bit go;\n"
      "  int n;\n"
      "  int woke_bare, woke_this, woke_expr;\n"
      "  task wait_bare();\n"
      "    wait (go) woke_bare = $time;\n"
      "  endtask\n"
      "  task wait_this();\n"
      "    wait (this.go) woke_this = $time;\n"
      "  endtask\n"
      "  task wait_expr();\n"
      "    wait (n == 2) woke_expr = $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    fork\n"
      "      h.wait_bare();\n"
      "      h.wait_this();\n"
      "      h.wait_expr();\n"
      "      begin\n"
      "        #3 h.n = 1;\n"
      "        #1 h.go = 1;\n"
      "        #2 h.n = 2;\n"
      "      end\n"
      "    join\n"
      "    result = h.woke_bare * 100 + h.woke_this * 10 + h.woke_expr;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 446u);
}

TEST(LevelSensitiveEventSimulation, WaitOnAQueueSizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (q.size() != 0);\n"
      "    v = q.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #10 q.push_back(7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 710u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnADynamicArraySizeCallIsReleasedByNew) {
  auto val = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    wait (d.size() == 3);\n"
      "    result = d.size() * 100 + $time;\n"
      "  end\n"
      "  initial #20 d = new[3];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 320u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnAQueuePropertySizeCallInsideAClassTaskIsReleasedByAPush) {
  auto val = RunAndGet(
      "class H;\n"
      "  int m_queue[$];\n"
      "  int first, second;\n"
      "  task get(output int v);\n"
      "    wait (m_queue.size() != 0);\n"
      "    v = m_queue.pop_front();\n"
      "  endtask\n"
      "  task run();\n"
      "    int v;\n"
      "    forever begin\n"
      "      get(v);\n"
      "      if (first == 0) first = v * 100 + $time;\n"
      "      else second = v * 100 + $time;\n"
      "    end\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  H h = new;\n"
      "  int result;\n"
      "  initial h.run();\n"
      "  initial begin\n"
      "    #10 h.m_queue.push_back(7);\n"
      "    #10 h.m_queue.push_back(9);\n"
      "    #1 result = h.first * 10000 + h.second;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 7100920u);
}

TEST(LevelSensitiveEventSimulation, WaitOnANonEmptyQueueSizeCallDoesNotBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(3);\n"
      "    wait (q.size() != 0);\n"
      "    result = q.pop_front() * 100 + $time;\n"
      "  end\n"
      "  initial #10 q.push_back(9);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 300u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnAStaticQueuePropertySizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "endclass\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (C::all.size() != 0);\n"
      "    v = C::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #15 C::all.push_back(4);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 415u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnABareStaticQueueInAStaticTaskIsReleasedByAStaticFunctionsPush) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "  static int result;\n"
      "  static task get();\n"
      "    int v;\n"
      "    wait (all.size() != 0);\n"
      "    v = all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  endtask\n"
      "  static function void put(int x);\n"
      "    all.push_back(x);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial C::get();\n"
      "  initial #20 C::put(9);\n"
      "  initial #30 result = C::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 920u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnAPackageClassStaticQueueSizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "package p;\n"
      "  class C;\n"
      "    static int all[$];\n"
      "  endclass\n"
      "endpackage\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (p::C::all.size() != 0);\n"
      "    v = p::C::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #30 p::C::all.push_back(5);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 530u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnAnInheritedStaticPropertyThroughTheDerivedClassIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    wait (D::n == 2);\n"
      "    result = C::n * 100 + $time;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 D::n = 1;\n"
      "    #5 D::n = 2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 210u);
}

TEST(LevelSensitiveEventSimulation,
     EventControlOnAnInheritedStaticPropertyWakesOnTheBaseClassWrite) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int woke;\n"
      "  initial @(D::n) woke = $time * 10 + C::n;\n"
      "  initial #7 C::n = 5;\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(val, 75u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnAnInheritedStaticQueueSizeCallIsReleasedByAPushThroughTheDerived) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (D::all.size() != 0);\n"
      "    v = D::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #10 D::all.push_back(7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 710u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnABareInheritedStaticQueueInADerivedStaticTaskIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "  static function void put(int x);\n"
      "    all.push_back(x);\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  static int result;\n"
      "  static task get();\n"
      "    int v;\n"
      "    wait (all.size() != 0);\n"
      "    v = all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial D::get();\n"
      "  initial #25 C::put(6);\n"
      "  initial #40 result = D::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 625u);
}

TEST(LevelSensitiveEventSimulation,
     WaitOnABareInheritedStaticPropertyInADerivedStaticTaskIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "  static int result;\n"
      "  static task get();\n"
      "    wait (n == 3);\n"
      "    result = n * 100 + $time;\n"
      "  endtask\n"
      "  static function void set(int x);\n"
      "    n = x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial D::get();\n"
      "  initial begin\n"
      "    #15 D::set(1);\n"
      "    #15 D::set(3);\n"
      "  end\n"
      "  initial #40 result = D::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 330u);
}

TEST(LevelSensitiveEventSimulation, WaitOnHierarchicalNameResumesWhenTrue) {
  SimFixture fp;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  int v = 0;\n"
                 "  initial begin #3 v = 1; #4 v = 3; end\n"
                 "  p pi();\n"
                 "endmodule\n"
                 "program p;\n"
                 "  initial begin\n"
                 "    wait (top.v == 3);\n"
                 "    $display(\"prog woke v=%0d at %0t\", top.v, $time);\n"
                 "  end\n"
                 "endprogram\n",
                 fp),
      "prog woke v=3 at 7\n");
  SimFixture fm;
  EXPECT_EQ(
      RunCapture("module sub;\n"
                 "  initial begin\n"
                 "    wait (top.v == 3);\n"
                 "    $display(\"sub woke v=%0d at %0t\", top.v, $time);\n"
                 "  end\n"
                 "endmodule\n"
                 "module top;\n"
                 "  int v;\n"
                 "  initial begin #3 v = 1; #4 v = 3; end\n"
                 "  sub s();\n"
                 "endmodule\n",
                 fm),
      "sub woke v=3 at 7\n");
}

}  // namespace
