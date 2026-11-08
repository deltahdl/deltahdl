#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EventControlSim, FunctionBodyWriteWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int woke;\n"
      "  function void poke(input logic [7:0] v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  always @(x) woke = woke + 1;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #1 poke(8'd2);\n"
      "    #1 poke(8'd3);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(EventControlSim, OutputFormalCopyOutWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] y;\n"
      "  int seen;\n"
      "  function void fill(output logic [7:0] o, input logic [7:0] v);\n"
      "    o = v;\n"
      "  endfunction\n"
      "  always @(y) seen = seen + 1;\n"
      "  initial begin\n"
      "    fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd9);\n"
      "    #1 fill(y, 8'd4);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "seen");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EventControlSim, PostfixIncrementWakesAnEventControl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  int hits;\n"
      "  always @(i) hits = hits + 1;\n"
      "  initial begin\n"
      "    #1 i++;\n"
      "    #1 i++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EventControlSim, PrefixAndDecrementSpellingsWakeAnEventControl) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] w;\n"
      "  int n;\n"
      "  always @(w) begin\n"
      "    n = n + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    w = 4'd7;\n"
      "    #1 ++w;\n"
      "    #1 --w;\n"
      "    #1 w--;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 4u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.ToUint64(), 6u);
}

TEST(EventControlSim, ForStepIncrementWakesAnEventControl) {
  SimFixture f;
  auto* taps = RunAndFindVar(
      "module t;\n"
      "  int k;\n"
      "  int taps;\n"
      "  always @(k) taps = taps + 1;\n"
      "  initial begin\n"
      "    #1;\n"
      "    for (k = 1; k < 4; k++) #1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "taps");
  ASSERT_NE(taps, nullptr);
  EXPECT_EQ(taps->value.ToUint64(), 4u);
  auto* k = f.ctx.FindVariable("k");
  ASSERT_NE(k, nullptr);
  EXPECT_EQ(k->value.ToUint64(), 4u);
}

TEST(EventControlSim, ForcedTargetIncrementWakesNoEventControl) {
  SimFixture f;
  auto* fired = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] p;\n"
      "  int fired;\n"
      "  initial begin\n"
      "    force p = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    @(p) fired = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 p++;\n"
      "    #1 p++;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "fired");
  ASSERT_NE(fired, nullptr);
  EXPECT_EQ(fired->value.ToUint64(), 0u);
  auto* p = f.ctx.FindVariable("p");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_forced);
  EXPECT_EQ(p->value.ToUint64(), 5u);
}

TEST(EventControlSim, MemberOfAnObjectThroughAHandleWakesAnEventControl) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "class Packet;\n"
      "  int status = 1;\n"
      "endclass\n"
      "module t;\n"
      "  Packet p, q;\n"
      "  int woke;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    q = p;\n"
      "    #2 q.status = 1;\n"
      "    #2 q.status = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    @(p.status) woke = $time * 10 + p.status;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 42u);
}

TEST(EventControlSim, OwnPropertyInsideAMethodWakesAnEventControl) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "class Mon;\n"
      "  int status;\n"
      "  bit flag;\n"
      "  int woke_bare, woke_this, woke_edge;\n"
      "  task wait_bare();\n"
      "    @(status) woke_bare = $time;\n"
      "  endtask\n"
      "  task wait_this();\n"
      "    @(this.status) woke_this = $time;\n"
      "  endtask\n"
      "  task wait_edge();\n"
      "    @(posedge flag) woke_edge = $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  Mon m;\n"
      "  int result;\n"
      "  initial begin\n"
      "    m = new;\n"
      "    m.flag = 1;\n"
      "    fork\n"
      "      m.wait_bare();\n"
      "      m.wait_this();\n"
      "      m.wait_edge();\n"
      "      begin\n"
      "        #3 m.status = 7;\n"
      "        #1 m.flag = 0;\n"
      "        #2 m.flag = 1;\n"
      "      end\n"
      "    join\n"
      "    result = m.woke_bare * 100 + m.woke_this * 10 + m.woke_edge;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 336u);
}

TEST(EventControlSim, StaticPropertyThroughTheClassScopeWakesAnEventControl) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "module t;\n"
      "  int woke;\n"
      "  initial begin\n"
      "    woke = 99;\n"
      "    @(C::n) woke = $time * 10 + C::n;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 C::n = 1;\n"
      "    #2 C::n = 2;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 21u);
}

TEST(EventControlSim, WaitOnAStaticPropertyThroughTheClassScopeResumes) {
  SimFixture f;
  auto* waited = RunAndFindVar(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "module t;\n"
      "  int waited;\n"
      "  initial begin\n"
      "    waited = 99;\n"
      "    wait (C::n == 2) waited = $time;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 C::n = 1;\n"
      "    #2 C::n = 2;\n"
      "  end\n"
      "endmodule\n",
      f, "waited");
  ASSERT_NE(waited, nullptr);
  EXPECT_EQ(waited->value.ToUint64(), 4u);
}

TEST(EventControlSim, StaticPropertyWrittenFromAStaticMethodWakesBothForms) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "class C;\n"
      "  static int n;\n"
      "  int woke_bare;\n"
      "  static function void set(int v);\n"
      "    n = v;\n"
      "  endfunction\n"
      "  task watch();\n"
      "    @(n) woke_bare = $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  int woke_scope, result;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    fork\n"
      "      c.watch();\n"
      "      @(C::n) woke_scope = $time * 10 + C::n;\n"
      "      #3 C::set(5);\n"
      "    join\n"
      "    result = woke_scope * 100 + c.woke_bare;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 3503u);
}

TEST(EventControlSim, AlwaysAtBareEventNameCountsEachTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int n;\n"
      "  always @e n++;\n"
      "  initial begin\n"
      "    #2 -> e;\n"
      "    #2 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EventControlSim, BareEventNameGuardsATrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e, f;\n"
      "  int got;\n"
      "  initial @e -> f;\n"
      "  initial @f got = 7;\n"
      "  initial begin\n"
      "    #2 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
