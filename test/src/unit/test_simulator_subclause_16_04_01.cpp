#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

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

}  // namespace
