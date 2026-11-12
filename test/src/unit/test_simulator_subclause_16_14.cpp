#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(ConcurrentAssertionStatements, APropertyOnItsOwnIsNeverEvaluated) {
  std::string out = RunAssertions(
      "  property idle;\n"
      "    @(posedge clk) 0;\n"
      "  endproperty\n"
      "  m_used: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n");
  EXPECT_EQ(out, "t.m_used failed at 15\n$finish at time 40\n");
}

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

TEST(ConcurrentAssertionStatements, AStatementStandsInAProgram) {
  std::string out = RunAssertions(
      "  program prog;\n"
      "    pr_named: assert property (@(posedge clk) a)\n"
      "      else $display(\"%m failed at %0d\", $time);\n"
      "  endprogram\n");
  EXPECT_EQ(out, "t.prog.pr_named failed at 15\n$finish at time 40\n");
}

TEST(ConcurrentAssertionStatements, ALabelOfOneProcessIsNotReportedByAnother) {
  std::string out = RunAssertions(
      "  initial begin : waiting\n"
      "    #100;\n"
      "  end\n"
      "  m_named: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed at %0d\", $time);\n");
  EXPECT_EQ(out, "t.m_named failed at 15\n$finish at time 40\n");
}

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

struct AssertOffResult {
  std::string out;
  bool has_errors;
};

AssertOffResult RunAssertOffCase(const std::string& name) {
  SimFixture f;
  std::string out = RunCapture(
      "module sub(input logic clk, input logic a);\n"
      "  a1: assert property (@(posedge clk) a)\n"
      "    else $display(\"%m failed\");\n"
      "  if (1) begin : gen\n"
      "    g1: assert property (@(posedge clk) a)\n"
      "      else $display(\"%m failed\");\n"
      "  end\n"
      "  always @(posedge clk) begin : proc\n"
      "    p1: assert property (a) else $display(\"%m failed\");\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  sub u(clk, a);\n"
      "  initial begin\n"
      "    $assertoff(0, " +
          name +
          ");\n"
          "    #10 a = 0;\n"
          "    #10 a = 1;\n"
          "    #20 $finish;\n"
          "  end\n"
          "endmodule\n",
      f);
  return {out, f.diag.HasErrors()};
}

void ExpectOnlyTheNamedStatementIsOff(const std::string& name,
                                      const std::string& off) {
  auto r = RunAssertOffCase(name);
  EXPECT_FALSE(r.has_errors) << name;
  for (const char* label : {"t.u.a1", "t.u.gen.g1", "t.u.proc.p1"}) {
    std::string line = std::string(label) + " failed\n";
    if (off == label) {
      EXPECT_EQ(r.out.find(line), std::string::npos) << name;
    } else {
      EXPECT_NE(r.out.find(line), std::string::npos) << name;
    }
  }
}

TEST(ConcurrentAssertionStatements, AHierarchicalNameReachesANamedStatement) {
  ExpectOnlyTheNamedStatementIsOff("t.u.a1", "t.u.a1");
  ExpectOnlyTheNamedStatementIsOff("t.u.gen.g1", "t.u.gen.g1");
  ExpectOnlyTheNamedStatementIsOff("u.gen.g1", "t.u.gen.g1");
  ExpectOnlyTheNamedStatementIsOff("t.u.proc.p1", "t.u.proc.p1");
  ExpectOnlyTheNamedStatementIsOff("u.proc.p1", "t.u.proc.p1");
}

TEST(ConcurrentAssertionStatements,
     DISABLED_ARelativeNameReachesAStatementOfAnInstanceWithNoBlock) {
  for (const char* off : {"a1", "m1"}) {
    SimFixture f;
    std::string out = RunCapture(
        "module sub(input logic clk, input logic a);\n"
        "  a1: assert property (@(posedge clk) a)\n"
        "    else $display(\"%m failed\");\n"
        "  m1: assume property (@(posedge clk) a)\n"
        "    else $display(\"%m failed\");\n"
        "endmodule\n"
        "module t;\n"
        "  logic clk = 0;\n"
        "  logic a = 1;\n"
        "  always #5 clk = ~clk;\n"
        "  sub u(clk, a);\n"
        "  initial begin\n"
        "    $assertoff(0, u." +
            std::string(off) +
            ");\n"
            "    #10 a = 0;\n"
            "    #10 a = 1;\n"
            "    #20 $finish;\n"
            "  end\n"
            "endmodule\n",
        f);
    EXPECT_FALSE(f.diag.HasErrors()) << off;
    std::string on = std::string(off) == "a1" ? "m1" : "a1";
    EXPECT_EQ(out, "t.u." + on + " failed\n$finish at time 40\n") << off;
  }
}

TEST(ConcurrentAssertionStatements,
     ARelativeNameReachesAStatementOfAnInstance) {
  ExpectOnlyTheNamedStatementIsOff("u.a1", "t.u.a1");
}

TEST(ConcurrentAssertionStatements, ASimpleNameReachesAStatementInItsScope) {
  EXPECT_EQ(RunAssertions("  m_off: assert property (@(posedge clk) a)\n"
                          "    else $display(\"%m failed\");\n"
                          "  m_on: assert property (@(posedge clk) a)\n"
                          "    else $display(\"%m failed\");\n"
                          "  initial $assertoff(0, m_off);\n"),
            "t.m_on failed\n$finish at time 40\n");
}

}  // namespace
