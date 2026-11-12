#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(AssertionStatementSim, DeferredAssertHash0) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x_44; x = 8'd44; endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) set_x_44();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(DeferredAssertionReporting, ObservedDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert #0 (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(DeferredAssertionReporting, FinalDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(DeferredAssertionReporting, DeferredAssumeDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assume #0 (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(DeferredAssertionReporting, FinalReportRunsAfterObservedReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (0) else $error(\"final\");\n"
      "    assert #0 (0) else $error(\"observed\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "final");
}

TEST(DeferredAssertionReporting, DeferredCoverActionIsPendingReport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int hits = 0;\n"
      "  function void bump; hits = hits + 1; endfunction\n"
      "  initial begin\n"
      "    cover #0 (1) bump();\n"
      "    hits = 5;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(DeferredAssertionReporting, FinalPassActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (1) $info(\"final pass\");\n"
      "    $error(\"inline\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
}

TEST(DeferredAssertionReporting, FinalCoverActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover final (1) $warning(\"covered late\");\n"
      "    $error(\"inline\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
}

TEST(DeferredAssertionReporting, PassingDeferredAssertProducesNoReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DeferredAssertionReporting,
     ReactiveRegionWriteReexecutesAnObservedDeferredAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a = 1;\n"
      "  task automatic note(input string s); $display(\"%s\", s); endtask\n"
      "  function void set_a_1; a = 1; endfunction\n"
      "  always_comb begin\n"
      "    assert #0 (a == 1) note(\"observed: a is 1\");\n"
      "    else note(\"observed: a is not 1\");\n"
      "    assert final (a == 1) note(\"final: a is 1\");\n"
      "    else note(\"final: a is not 1\");\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 2;\n"
      "    cover #0 (1) set_a_1();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "observed: a is 1\nfinal: a is 1\n"
            "observed: a is not 1\nobserved: a is 1\nfinal: a is 1\n");
}

TEST(DeferredAssertionReporting, DeferredDefaultErrorNamesTheAssertionsScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : b1\n"
      "    a1: assert #0 (0);\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityScope(), "t.b1.a1");
  EXPECT_EQ(f.ctx.LastSeverityLine(), 3u);
}

const char kShow[] =
    "  task automatic show(input string s, input int x);\n"
    "    $display(\"%s v=%0d\", s, x);\n"
    "  endtask\n"
    "  task automatic note(input string s); $display(\"%s\", s); endtask\n";

std::string InInitial(const std::string& stmts) {
  return std::string("module t;\n  int v, c = 1;\n") + kShow +
         "  initial begin\n" + stmts + "  end\nendmodule\n";
}

TEST(DeferredAssertionReporting,
     AnAssumeFinalPassActionRunsInThePostponedRegion) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(InInitial("    v = 1;\n"
                           "    assume final (v == 1) show(\"pass\", v);\n"
                           "    v = 5;\n"
                           "    $display(\"active done\");\n"),
                 f),
      "active done\npass v=1\n");
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DeferredAssertionReporting, AnAssumeFailActionIsAPendingReport) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                InInitial("    v = 1;\n"
                          "    assume final (v == 2) else show(\"final\", v);\n"
                          "    assume #0 (v == 2) else show(\"observed\", v);\n"
                          "    v = 5;\n"
                          "    $display(\"active done\");\n"),
                f),
            "active done\nobserved v=1\nfinal v=1\n");
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

TEST(DeferredAssertionReporting, AnAssumeFinalDefaultErrorReportIsDeferred) {
  SimFixture f;
  RunCapture(InInitial("    assume final (0);\n"
                       "    $warning(\"later\");\n"),
             f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

TEST(DeferredAssertionReporting, AFailWithOnlyAPassStatementQueuesTheError) {
  for (const char* form :
       {"assert #0", "assert final", "assume #0", "assume final"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(InInitial(std::string("    ") + form +
                                   " (0) note(\"pass ran\");\n"
                                   "    $warning(\"later\");\n"),
                         f),
              "[0] WARNING t (<test>:9): later\n")
        << form;
    EXPECT_EQ(f.ctx.LastSeverity(), "ERROR") << form;
    EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.") << form;
  }
}

TEST(DeferredAssertionReporting, APassWithNoStatementQueuesNothing) {
  for (const char* stmt :
       {"assert final (1);", "assume #0 (1);", "assume final (1);"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(InInitial(std::string("    ") + stmt + "\n"), f), "")
        << stmt;
    EXPECT_EQ(f.ctx.LastSeverity(), "") << stmt;
  }
}

TEST(DeferredAssertionReporting, ADeferredCoverWithNoStatementStillCounts) {
  SimFixture f;
  EXPECT_EQ(RunCapture(InInitial("    c0: cover #0 (1);\n"
                                 "    c1: cover final (1);\n"),
                       f),
            "");
  const auto& results = f.ctx.ImmediateCovers().Results();
  ASSERT_EQ(results.size(), 2u);
  for (const auto& r : results) {
    EXPECT_EQ(r.evaluated, 1u) << r.scope;
    EXPECT_EQ(r.succeeded, 1u) << r.scope;
  }
}

TEST(DeferredAssertionReporting, APassOfAnElseOnlyAssertionQueuesNothing) {
  for (const char* form : {"assert final", "assume #0", "assume final"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(InInitial(std::string("    ") + form +
                                   " (c == 1) else note(\"fail ran\");\n"),
                         f),
              "")
        << form;
    EXPECT_EQ(f.ctx.LastSeverity(), "") << form;
  }
}

TEST(DeferredAssertionReporting,
     AnObservedReportRunsAfterTheNbaAndInactiveWork) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic x = 0;\n"
                       "  task automatic note(input string s); "
                       "$display(\"%s\", s); endtask\n"
                       "  always @(x) $display(\"nba update seen\");\n"
                       "  initial begin\n"
                       "    assert final (1) note(\"final report\");\n"
                       "    assert #0 (1) note(\"observed report\");\n"
                       "    x <= 1;\n"
                       "  end\n"
                       "  initial #0 $display(\"inactive\");\n"
                       "endmodule\n",
                       f),
            "inactive\nnba update seen\nobserved report\nfinal report\n");
}

}  // namespace
