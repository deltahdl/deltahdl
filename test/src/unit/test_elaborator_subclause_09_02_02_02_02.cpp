#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysCombVsAlwaysStar, AlwaysStarIsAlwaysKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always @* y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlways);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarNoMultiDriverError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, y;\n"
      "  always @* y = a;\n"
      "  always @* y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsTimingControl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  always @(posedge clk) a = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysCombRejectsTimingControl) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  always_comb #5 a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombExtendedSim, AlwaysCombConstAssignTime0) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] y;\n"
      "  always_comb y = 42;\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(AlwaysStarSim, AlwaysStarEquivAlwaysComb) {
  SimFixture f_star;
  auto* d_star = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_star);
  ASSERT_NE(d_star, nullptr);

  Lowerer lowerer_star(f_star.ctx, f_star.arena, f_star.diag);
  lowerer_star.Lower(d_star);
  f_star.scheduler.Run();

  SimFixture f_comb;
  auto* d_comb = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a ^ b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'h55;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f_comb);
  ASSERT_NE(d_comb, nullptr);

  Lowerer lowerer_comb(f_comb.ctx, f_comb.arena, f_comb.diag);
  lowerer_comb.Lower(d_comb);
  f_comb.scheduler.Run();

  auto* y_star = f_star.ctx.FindVariable("y");
  auto* y_comb = f_comb.ctx.FindVariable("y");
  ASSERT_NE(y_star, nullptr);
  ASSERT_NE(y_comb, nullptr);
  EXPECT_EQ(y_star->value.ToUint64(), y_comb->value.ToUint64());
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, EventControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb @(posedge clk) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not have an explicit event control", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, EmbeddedEventControlInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_comb begin\n"
      "    a = 1;\n"
      "    @(posedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsEmbeddedEventControl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always @* begin\n"
      "    a = 1;\n"
      "    @(posedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, WaitInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready, a;\n"
      "  always_comb wait (ready) a = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, WaitForkInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    a = 1;\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsWaitFork) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always @* begin\n"
      "    a = 1;\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsForkJoin) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsWait) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic ready, a;\n"
      "  always @* wait (ready) a = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, JoinAnyInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, JoinNoneInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsJoinAny) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysStarAllowsJoinNone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @* begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AlwaysCombVsAlwaysStar, AlwaysCombRejectsNestedDelay) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      #1 a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, CycleDelayInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    ##3 q = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, WaitOrderInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  event a, b;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    wait_order(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 4,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, ExpectInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, ready, q;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    expect (@(posedge clk) ready);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, NonblockingEventTriggerInAlwaysCombAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  event ev;\n"
      "  always_comb begin\n"
      "    q = 0;\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n",
      f);
  std::string cited;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError && diag.subclause == "9.2.2.2.2")
      cited = diag.message;
  }
  EXPECT_TRUE(cited.empty())
      << "an error cites §9.2.2.2.2 against a nonblocking event trigger, "
         "which §15.5.1 rules executes without blocking: "
      << cited;
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInAnAssertionPassStatementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) fork y = a; join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInAnAssertionFailStatementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a; else fork y = 1'b0; join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInARandcaseItemErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randcase\n"
      "      1: fork y = a; join\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, ForkJoinInARandsequenceCodeBlockErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randsequence(main)\n"
      "      main : { fork y = a; join };\n"
      "    endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "always_comb shall not contain fork-join statements", 3, "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, DelayInAnAssertionPassStatementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) #5 y = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, DelayInAnAssertionFailStatementErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb assert (a) y = a; else #5 y = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, DelayInARandcaseItemErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randcase\n"
      "      1: #5 y = a;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, DelayInARandsequenceCodeBlockErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, y;\n"
      "  always_comb\n"
      "    randsequence(main)\n"
      "      main : { #5 y = a; };\n"
      "    endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain timing controls", 3,
                            "9.2.2.2.2"));
}

TEST(AlwaysCombVsAlwaysStar, BlockingIntraAssignmentTimingIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic a, c, d, e, y, q, z, w;\n"
      "  always_comb y = #1 a;\n"
      "  always_latch w = @(d) a;\n"
      "  always_ff @(posedge c) q = @(d) e;\n"
      "  always_comb z <= #1 a;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "always_comb shall not contain timing controls", 2, "9.2.2.2.2"));
  EXPECT_TRUE(ReportedError(
      diags, "always_latch shall not contain timing controls", 3, "9.2.2.3"));
  EXPECT_TRUE(ReportedError(diags,
                            "always_ff shall not contain blocking timing "
                            "controls",
                            4, "9.2.2.4"));
  EXPECT_FALSE(ReportedError(diags, "shall not contain", 5, "9.2.2.2.2"));
}

}  // namespace
