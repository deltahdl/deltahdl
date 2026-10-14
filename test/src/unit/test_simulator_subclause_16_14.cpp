#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A module around one or more concurrent assertion statements, as
// test/src/e2e/concurrent_assertion_statements.sv is: clk rises at 5, 15,
// 25 and 35, and a is low across the tick at 15 alone; the run ends at 40.
std::string AssertionSource(const std::string& items,
                            const std::string& before = "") {
  return before +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 1;\n"
         "  always #5 clk = ~clk;\n" +
         items +
         "  initial begin\n"
         "    #10 a = 0;\n"
         "    #10 a = 1;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

std::string RunAssertions(const std::string& items,
                          const std::string& before = "") {
  SimFixture f;
  return RunCapture(AssertionSource(items, before), f);
}

// §16.14: a named statement's name is a level of the hierarchical name its
// action block reports through %m, and an unnamed statement creates no
// scope, so %m there names the module alone.
TEST(ConcurrentAssertionStatements,
     ANamedStatementIsAScopeAndAnUnnamedOneIsNot) {
  std::string out = RunAssertions(
      "  m_named: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "  assert property (@(posedge clk) a)\n"
      "    else $display(\"%m unnamed failed at %0d\", $time);\n");
  EXPECT_NE(out.find("t.m_named failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t unnamed failed at 15\n"), std::string::npos);
}

// §16.14: the five statement kinds: assert and assume execute their fail
// statements where the property is false, cover property and cover
// sequence their pass statements where it holds or the sequence matches,
// and restrict property nothing.
TEST(ConcurrentAssertionStatements, TheFiveStatementKinds) {
  std::string out = RunAssertions(
      "  m_assert: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "  m_assume: assume property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "  m_cover: cover property (@(posedge clk) !a)\n"
      "    $display(\"%m covered at %0d\", $time);\n"
      "  m_cover_seq: cover sequence (@(posedge clk) a ##1 !a)\n"
      "    $display(\"%m covered at %0d\", $time);\n"
      "  m_restrict: restrict property (@(posedge clk) !a);\n");
  EXPECT_NE(out.find("t.m_assert failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.m_assume failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.m_cover covered at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.m_cover_seq covered at 15\n"), std::string::npos);
  EXPECT_EQ(out.find("m_restrict"), std::string::npos);
}

// §16.14: a property on its own is never evaluated: one declared and never
// used in an assertion statement, false at every tick, reports nothing.
TEST(ConcurrentAssertionStatements, APropertyOnItsOwnIsNeverEvaluated) {
  std::string out = RunAssertions(
      "  property idle;\n"
      "    @(posedge clk) 0;\n"
      "  endproperty\n"
      "  m_used: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n");
  EXPECT_EQ(out, "t.m_used failed at 15\n$finish at time 40\n");
}

// §16.14: a concurrent assertion statement may stand in a generate block,
// an always procedure, an interface and a checker, each a scope of the
// hierarchical name its action block reports.
TEST(ConcurrentAssertionStatements,
     AStatementStandsInAGenerateBlockAProcedureAnInterfaceAndAChecker) {
  std::string out = RunAssertions(
      "  bus_if bus(clk, a);\n"
      "  chk u_chk(clk, a);\n"
      "  generate\n"
      "    if (1) begin : gen\n"
      "      g_named: assert property (@(posedge clk) a)\n"
      "        else $display(\"%m failed at %0d\", $time);\n"
      "    end\n"
      "  endgenerate\n"
      "  always @(posedge clk) begin : proc\n"
      "    p_named: assert property (a)\n"
      "      else $display(\"%m failed at %0d\", $time);\n"
      "  end\n",
      "interface bus_if(input logic clk, input logic f);\n"
      "  if_named: assert property (@(posedge clk) f)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "endinterface\n"
      "checker chk(input logic clk, input logic g);\n"
      "  chk_named: assert property (@(posedge clk) g)\n"
      "    else $display(\"%m failed at %0d\", $time);\n"
      "endchecker\n");
  EXPECT_NE(out.find("t.gen.g_named failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.proc.p_named failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.bus.if_named failed at 15\n"), std::string::npos);
  EXPECT_NE(out.find("t.u_chk.chk_named failed at 15\n"), std::string::npos);
}

// §16.14: a concurrent assertion statement may stand in a program, a scope
// of the hierarchical name its action block reports.
TEST(ConcurrentAssertionStatements, AStatementStandsInAProgram) {
  std::string out = RunAssertions(
      "  program prog;\n"
      "    pr_named: assert property (@(posedge clk) a)\n"
      "      else $display(\"%m failed at %0d\", $time);\n"
      "  endprogram\n");
  EXPECT_EQ(out, "t.prog.pr_named failed at 15\n$finish at time 40\n");
}

// §21.2.1.5 by way of §16.14: the label a procedure stands inside is that
// procedure's level alone, so a statement of the module reports none of
// another process's labels.
TEST(ConcurrentAssertionStatements, ALabelOfOneProcessIsNotReportedByAnother) {
  std::string out = RunAssertions(
      "  initial begin : waiting\n"
      "    #100;\n"
      "  end\n"
      "  m_named: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n");
  EXPECT_EQ(out, "t.m_named failed at 15\n$finish at time 40\n");
}

// §16.14 and §27: a static concurrent assertion in a generate loop is
// attempted at every tick of its clock, as one at module level is, whether the
// clock is written on it, taken from the default clocking (§14.12), or the
// operand is indexed by the genvar. a is low at the rises of 25, 45 and 55
// alone, so each of the four fails three times.
TEST(ConcurrentAssertionStatements, AStatementInAGenerateLoopIsAttempted) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111;\n"
      "  always @(negedge clk) av <= av << 1;\n"
      "  bit a; assign a = av[0];\n"
      "  logic [1:0] v; assign v = {a, a};\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  int f0 = 0;\n"
      "  assert property (a) else f0++;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g1\n"
      "    int f = 0;\n"
      "    assert property (@(posedge clk) a) else f++;\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : g2\n"
      "    int f = 0;\n"
      "    assert property (a) else f++;\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : g3\n"
      "    int f = 0;\n"
      "    assert property (@(posedge clk) v[i]) else f++;\n"
      "  end\n"
      "  initial #98 $display(\"f0=%0d f1=%0d f2=%0d f3=%0d\", f0, g1[0].f, "
      "g2[0].f, g3[0].f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f0=3 f1=3 f2=3 f3=3\n");
}

// Each iteration of a generate loop holds an assertion of its own, reading its
// own bit of v: bit 0 is low at three rises, bit 1 at the first five and bit 2
// never, so the three instances fail three, five and no times.
TEST(ConcurrentAssertionStatements,
     EachGenerateIterationIsAnAssertionOfItsOwn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0000011111;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  logic [2:0] v; assign v = {1'b1, bv[0], av[0]};\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  for (genvar i = 0; i < 3; i++) begin : g\n"
      "    int f = 0;\n"
      "    assert property (v[i]) else f++;\n"
      "  end\n"
      "  initial #98 $display(\"f0=%0d f1=%0d f2=%0d\", g[0].f, g[1].f, "
      "g[2].f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "f0=3 f1=5 f2=0\n");
}

// §16.14: a concurrent assertion is a module item whatever the module's ports
// are, so one reading an interface through a modport port or a port of the
// interface's type, its clock the interface's own port, is attempted at every
// tick. req is high at the rises of 15 and 45 and gnt at 25 alone, so the
// attempt of 15 passes, that of 45 fails at 55 and the other eight pass
// vacuously.
TEST(ConcurrentAssertionStatements, AStatementReadsThroughAnInterfacePort) {
  SimFixture f;
  std::string out = RunCapture(
      "interface bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  modport mon(input clk, input req, input gnt);\n"
      "endinterface\n"
      "module chk_mp(bus.mon m);\n"
      "  int p = 0, f = 0;\n"
      "  assert property (@(posedge m.clk) m.req |=> m.gnt) p++; else f++;\n"
      "endmodule\n"
      "module chk_plain(bus m);\n"
      "  int p = 0, f = 0;\n"
      "  assert property (@(posedge m.clk) m.req |=> m.gnt) p++; else f++;\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  bus b(clk);\n"
      "  assign b.req = av[0]; assign b.gnt = bv[0];\n"
      "  chk_mp u1(b.mon);\n"
      "  chk_plain u2(b);\n"
      "  initial #98 $display(\"p=%0d f=%0d p2=%0d f2=%0d\", u1.p, u1.f, "
      "u2.p, u2.f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=9 f=1 p2=9 f2=1\n");
}

}  // namespace
