#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kTiming = "final procedure shall not contain timing controls";
const char* const kFork =
    "final procedure shall not contain fork-join statements";

TEST(CheckerFinalContents, EachConstructAModuleFinalRefusesIsReported) {
  const std::string kSrc =
      "package pk; task t; endtask endpackage\n"
      "task u; endtask\n"
      "checker chk(logic a, event e);\n"
      "  final $display(\"ok\");\n"
      "  final @(e) $display(\"ev\");\n"
      "  final wait (a) $display(\"wt\");\n"
      "  final wait fork;\n"
      "  final begin int k; k = #1 1; end\n"
      "  final begin int k; k = @(e) 1; end\n"
      "  final fork $display(\"fj\"); join\n"
      "  final fork $display(\"fa\"); join_any\n"
      "  final pk::t();\n"
      "  final u();\n"
      "endchecker\n"
      "module top;\n"
      "  logic a;\n"
      "  event e;\n"
      "  chk c(a, e);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  const auto& diags = f.diag.Diagnostics();
  EXPECT_FALSE(ErrorOnLine(diags, 4));
  for (int line : {5, 6, 7, 8, 9}) {
    EXPECT_TRUE(ReportedError(diags, kTiming, line, "9.2.3")) << line;
  }
  EXPECT_TRUE(ReportedError(diags, kFork, 10, "9.2.3"));
  EXPECT_TRUE(ReportedError(diags, kFork, 11, "9.2.3"));
  EXPECT_TRUE(ReportedError(diags, "final procedure enables task 'pk::t'", 12,
                            "9.2.3"));
  EXPECT_TRUE(
      ReportedError(diags, "final procedure enables task 'u'", 13, "9.2.3"));
}

TEST(CheckerFinalContents, StatementsAnInitialMayNotHoldAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(logic a);\n"
      "  function int twice(int v); return 2 * v; endfunction\n"
      "  final begin\n"
      "    if (a) $display(\"if\"); else $display(\"else\");\n"
      "    case (a) 1'b1: $display(\"one\"); default: $display(\"zero\"); "
      "endcase\n"
      "    for (int i = 0; i < 2; i++) $display(\"%0d\", i);\n"
      "    a1: assert (a) $display(\"pass\"); else $display(\"fail\");\n"
      "    $display(\"%0d\", twice(3));\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic a;\n"
      "  chk c(a);\n"
      "endmodule\n",
      f, "top");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

const char* const kNoClock =
    "no clock is inferred for the procedural concurrent assertion";

TEST(CheckerProceduralConcurrentClock, AnUnclockedCombAssertionIsReported) {
  const std::string kSrc =
      "checker chk(logic a, clk);\n"
      "  always_comb a1: assert property (a);\n"
      "endchecker\n"
      "checker dchk(logic a, clk);\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  always_comb a2: assert property (a);\n"
      "  always_latch if (clk) a3: assert property (a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic a, clk;\n"
      "  chk c(a, clk);\n"
      "  dchk d(a, clk);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kNoClock, 2, "16.14.6"));
  EXPECT_FALSE(ErrorOnLine(diags, 6));
  EXPECT_FALSE(ErrorOnLine(diags, 7));
}

TEST(CheckerProceduralConcurrentClock,
     DISABLED_AnEventFormalsEdgeActualClocksIt) {
  const std::string kSrc =
      "checker c1(event clk);\n"
      "  int n = 0;\n"
      "  always_ff @(clk) begin\n"
      "    n <= n + 1;\n"
      "    p0: assert property (n < 3);\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  event ev;\n"
      "  c1 u(posedge clk);\n"
      "  c1 w(ev);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
