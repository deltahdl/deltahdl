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

std::string Run(const std::string& items, const std::string& before = "") {
  SimFixture f;
  return RunCapture(AssertionSource(items, before), f);
}

// §16.14: a named statement's name is a level of the hierarchical name its
// action block reports through %m, and an unnamed statement creates no
// scope, so %m there names the module alone.
TEST(ConcurrentAssertionStatements,
     ANamedStatementIsAScopeAndAnUnnamedOneIsNot) {
  std::string out =
      Run("  m_named: assert property (@(posedge clk) a)\n"
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
  std::string out =
      Run("  m_assert: assert property (@(posedge clk) a)\n"
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
  std::string out =
      Run("  property idle;\n"
          "    @(posedge clk) 0;\n"
          "  endproperty\n"
          "  m_used: assert property (@(posedge clk) a)\n"
          "    else $display(\"%m failed at %0d\", $time);\n");
  EXPECT_EQ(out, "t.m_used failed at 15\n");
}

// §16.14: a concurrent assertion statement may stand in a generate block,
// an always procedure, an interface and a checker, each a scope of the
// hierarchical name its action block reports.
TEST(ConcurrentAssertionStatements,
     AStatementStandsInAGenerateBlockAProcedureAnInterfaceAndAChecker) {
  std::string out =
      Run("  bus_if bus(clk, a);\n"
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

// §16.14: a statement in an initial procedure, of the module or of a
// program, is executed once, so it runs one attempt, at the next tick.
TEST(ConcurrentAssertionStatements,
     AStatementInAnInitialProcedureRunsOneAttempt) {
  std::string out =
      Run("  initial begin : init\n"
          "    #10;\n"
          "    i_named: assert property (@(posedge clk) a)\n"
          "      else $display(\"%m failed at %0d\", $time);\n"
          "  end\n"
          "  program prog;\n"
          "    initial begin\n"
          "      pr_named: assert property (@(posedge clk) 0)\n"
          "        else $display(\"%m failed at %0d\", $time);\n"
          "      #50;\n"
          "    end\n"
          "  endprogram\n");
  EXPECT_EQ(out,
            "t.prog.pr_named failed at 5\n"
            "t.init.i_named failed at 15\n");
}

}  // namespace
